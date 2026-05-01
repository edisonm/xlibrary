/*  Part of Extended Libraries for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xlibrary
    Copyright (C): 2026, Process Design Center, Breda, The Netherlands.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(local_dynamic,
          [ % context
            with_local_dynamic/2,
            with_local_dynamic/3,

            % mutation
            ld_asserta/2,
            ld_assertz/2,
            ld_retract/2,
            ld_retractall/2,

            % querying
            ld_call/2
    
          ]).

/** <module> local_dynamic

Scoped dynamic predicates.

This module provides a disciplined way to use dynamic predicates with a
well-defined scope and lifetime.  Dynamic predicates declared through
with_local_dynamic/2 or with_local_dynamic/3 exist only for the duration
of a goal and are automatically cleaned up on exit, regardless of
success, failure, or exception.

The intent is to allow temporary or working-memory-style use of dynamic
predicates without relying on global state, while preserving normal
Prolog semantics such as backtracking, logical update semantics, and
indexing (JITI).

A local dynamic context is introduced using with_local_dynamic/… .
Within this context, predicates described by a schema (a list of
Name/Arity pairs, optionally module-qualified) may be asserted,
retracted, and called using the ld_* predicates.  Outside the context,
these predicates are not visible logically.

Dynamic predicate definitions are reused internally and cleared using
retractall/1 with most-general heads.  This avoids unbounded growth of
dynamic predicate definitions, keeps cleanup efficient, and preserves
predicate identity and indexing across invocations.

Contexts are thread-local: each thread has its own independent set of
local dynamic predicates.  No synchronization is required between
threads, but it is the caller’s responsibility to ensure that a local
dynamic context is not accessed after its scope has ended.

The public API mirrors Prolog’s built-in dynamic database predicates:

  * with_local_dynamic/2,3   – introduce a local dynamic scope
  * ld_asserta/1,2           – scoped asserta/1
  * ld_assertz/1,2           – scoped assertz/1
  * ld_call/1,2              – scoped call/1
  * ld_retract/1,2           – scoped retract/1
  * ld_retractall/1,2        – scoped retractall/1

Implicit ld_* operations refer to the most recently entered local
dynamic context; explicit forms accept a Scope argument to select a
specific context.

This module is intended for temporary data, working memories, rule
engines, planners, and similar patterns where dynamic predicates are
convenient but global visibility is undesirable.
*/

:- meta_predicate with_local_dynamic(:, -, 0).
:- meta_predicate with_local_dynamic(:, 0).

/*
  ld_relation(Store, Pattern, Pred, Module)

  Store   : store identifier (atom)
  Pattern : relation Pattern
  Pred    : internal predicate head
  Module  : context module
*/

:- thread_local ld_relation/4.
:- volatile ld_relation/4.

% Keep a pool of released predicates for reusage
:- thread_local ld_released/3.
:- volatile ld_released/3.

% private API lifecycle

%!  ld_new(+Schema, +M, -Store)
%
%   Create a new store.
%   Schema is a list of Name/Arity pairs.
%
ld_new(Schema, M, Store) :-
    must_be(list, Schema),
    gensym(ld_, Store),
    forall(
        member(Name/Arity, Schema),
        ld_define_relation(Store, M, Name, Arity)
    ).

ld_define_relation(Store, M, Name, Arity) :-
    must_be(atom, Name),
    must_be(integer, Arity),
    functor(Patt, Name, Arity),
    (   retract(ld_released(Patt, M, Term))
    ->  true
    ;   gensym(Name, Pred),
        Patt =.. [Name | Args],
        Term =.. [Pred | Args],
        thread_local(M:Pred/Arity)
    ),
    % NOTE:
    % ld_relation/4 entries are asserted with asserta/1 so that
    % implicit operations (ld_assertz/1, ld_query/1, etc.)
    % always target the most recently entered with_local_dynamic/… scope.
    asserta(ld_relation(Store, Patt, M, Term)).

%!  ld_free(+Store)
%
%   Destroy a store and all its data,
%   remove all data from all patterns in the store, and
%   Add the released relations to the released table
%

ld_free(Store) :-
    forall(
        retract(ld_relation(Store, Patt, M, Term)),
        (   retractall(M:Term),
            asserta(ld_released(Patt, M, Term))
        )).

%!  with_local_dynamic(:Schema, :Goal) is det.
%!  with_local_dynamic(:Schema, -Scope, :Goal) is det.
%
%   Execute Goal in a context where the dynamic predicates described
%   by Schema exist only locally and for the duration of Goal.
%
%   Schema is a list of Name/Arity pairs (optionally module-qualified)
%   defining the relations available in the local dynamic context.
%   Any clauses asserted into these predicates are visible only within
%   Goal and are automatically removed on exit, regardless of success,
%   failure, or exception.
%
%   Predicates in the schema are reused across invocations and cleared
%   using retractall/1, avoiding unbounded growth of dynamic predicate
%   definitions and preserving indexing (JITI) information.
%
%   Scope, when provided, is an identifier for the local dynamic context
%   and can be used with the explicit ld_* predicates.  If omitted, the
%   most recently entered local dynamic context is used implicitly.
%
%   This predicate provides scoped, thread-local dynamic predicates and
%   is intended as a disciplined alternative to using global dynamics
%   for temporary or working-memory data.

with_local_dynamic(M:Schema, Store, Goal) :-
    setup_call_cleanup(
        ld_new(Schema, M, Store),
        Goal,
        ld_free(Store)
    ).

%!  ld_assertz(+Store, +Fact)
%
%   Insert a fact at the end in the store
%
ld_assertz(Store, Fact) :-
    ld_pred(Store, Fact, Term),
    assertz(Term).

%!  ld_asserta(+Store, +Fact)
%
%   Insert a fact at the beginning in the store
%
ld_asserta(Store, Fact) :-
    ld_pred(Store, Fact, Term),
    asserta(Term).

%!  ld_retract(+Store, +Pattern)
%
%   Delete a fact matching Pattern from the store.
%   Could retract more facts on backtracking
%
ld_retract(Store, Pattern) :-
    ld_pred(Store, Pattern, Term),
    retract(Term).

%!  ld_retractall(+Store, +Pattern)
%
%   Delete all facts matching Pattern from the store.
%
ld_retractall(Store, Pattern) :-
    ld_pred(Store, Pattern, Term),
    retractall(Term).

%!  ld_call(+Store, +Pattern)
%
%   Query a pattern nondeterministically.
%
ld_call(Store, Pattern) :-
    ld_pred(Store, Pattern, Term),
    call(Term).

with_local_dynamic(Schema, Goal) :-
    with_local_dynamic(Schema, _, Goal).

ld_asserta(Fact) :-
    ld_asserta(_, Fact).

ld_assertz(Fact) :-
    ld_assertz(_, Fact).

%!  ld_pred(+Store, +Pattern, -Term)
%
%   Resolve the internal predicate for a fact.
%
ld_pred(Store, Pattern, M:Term) :-
    ld_relation(Store, Pattern, M, Term),
    !.
ld_pred(Store, Pattern, _) :-
    domain_error(local_dynamic(Store), Pattern).

/*
example :-
    with_local_dynamic([edge/2], S1,
        with_local_dynamic([edge/2], S2,
            (   ld_assertz(S1, edge(a,b)),
                ld_assertz(S2, edge(b,c)),

                ld_call(S1, edge(X,Y)),
                format("S1: ~w -> ~w~n", [X,Y]),

                ld_call(S2, edge(U,V)),
                format("S2: ~w -> ~w~n", [U,V]),

                ld_call(edge(M,N)),
                format("S3: ~w -> ~w~n", [M,N])
            )
        )).
*/
