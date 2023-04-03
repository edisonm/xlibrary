/*  Part of Extended Libraries for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xlibrary
    Copyright (C): 2014, Process Design Center, Breda, The Netherlands.
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

:- module(i18n_expansion, []).

:- reexport(library(compound_expand)).
:- reexport(library(i18n/i18n_op)).
:- use_module(library(i18n/i18n_support)).
:- init_expansors.

:- multifile
    translate_decl_hook/1.

translate_args(Meta, M, Goal1, Goal) :-
    functor(Meta, F, A),
    functor(Goal, F, A),
    translate_arg(1, Meta, M, Goal1, Goal).

translate_arg(N, Meta, M, Goal1, Goal) :-
    arg(N, Meta, Spec), !,
    arg(N, Goal1, Term1),
    arg(N, Goal,  Term),
    translate_non_goal_term(Spec, M, Term1, Term),
    succ(N, N1),
    translate_arg(N1, Meta, M, Goal1, Goal).
translate_arg(_, _, _, _, _).

translate_non_goal_term(S, _, Term, Term) :-
    '$expand':direct_call_meta_arg(S), !.
translate_non_goal_term(S, M, Term1, Term) :-
    translate_term(S, M, Term1, Term).

translate_term(S, M, Term1, Term) :-
    '$expand':meta_arg(S), !,
    translate_term_meta(M, Term1, Term).
translate_term(_, M, Term1, Term) :-
    translate_term(M, Term1, Term).

translate_term_meta(_, Term1, M:Term) :-
    nonvar(Term1),
    Term1 = M:Term2, !,
    translate_term_meta(M, Term2, Term).
translate_term_meta(M, Term1, Term) :-
    translate_term(M, Term1, Term).

gtabling(Elem, Goal) :-
    ( \+ Elem->
      ( Goal,
        compile_aux_clauses(Elem),
        fail
      ; true
      )
    ; true
    ).

tabulate_i18n_records(M) :-
    gtabling(i18n_support:i18n_record(M, L, I, S),
             current_i18n_record(M, L, I, S)).

translate_term(Term1, Term) :-
    '$current_source_module'(M),
    translate_term(M, Term1, Term),
    Term1 \== Term.

translate_term(M, Term1, Term) :-
    tabulate_i18n_records(M),
    expand_i18n_term(i18n_entry_expander, M, Term1, Term).

goal_expansion(V:Goal1, M, V:Goal) :-
    var(M), !,
    translate_term(M, Goal1, Goal).
goal_expansion(M:Goal1, _, M:Goal) :- !,
    goal_expansion(Goal1, M, Goal).
goal_expansion(Goal1, M, Goal) :-
    ( predicate_property(M:Goal1, meta_predicate(Meta))
    ->translate_args(Meta, M, Goal1, Goal)
    ; translate_term(M, Goal1, Goal)
    ), !,
    Goal1 \== Goal.

goal_expansion(Goal1, Goal) :-
    callable(Goal1),
    '$current_source_module'(M),
    goal_expansion(Goal1, M, Goal).

/* Commented out due to this cause cyclic terms when clause_info is
 * executed over this predicate itself:

goal_expansion(A=~B1, A=B) :-
    nonvar(B1), !,
    translate_term(~B1, B).
goal_expansion(A=~~B1, A=B) :-
    nonvar(B1), !,
    translate_term(~~B1, B).
goal_expansion(A = IB, A=~B) :-
    nonvar(IB),
    IB = ~(B), !.
goal_expansion(A = IB, G) :- % A bit complex due to static optimizations:
    nonvar(IB),
    IB = ~~(B),
    ( language(en),
      dictionary(Dict),
      en \= Dict
    ->G = (A~=B)
    ; language(Lang),
      dictionary(Lang),
      \+ ((dictionary(Dict2), Dict2 \= Lang))
    ->G = (A = B)
    ; language(en),
      \+ dictionary(_)
    ->G = (A = B)
    ; G = (A=~~B)
    ).
*/

term_expansion((:- i18n_resource(PoAlias)),
               i18n_support:i18n_resource(M, PoAlias)) :- !,
    '$current_source_module'(M).
term_expansion((:- resourceterm(Term)),
               i18n_support:i18n_resourceterm(M, Term)) :- !,
    '$current_source_module'(M).
term_expansion((:- init_i18n),
               []) :- !,
    '$current_source_module'(M),
    tabulate_i18n_records(M).
term_expansion((:- M:init_i18n), [])  :- !, tabulate_i18n_records(M).
term_expansion((:- init_i18n(M)), []) :- !, tabulate_i18n_records(M).
term_expansion((:- Decl), _) :-
    \+ translate_decl_hook(Decl),
    !,
    fail. % Skip declarations
term_expansion((Term1 :- Body), (Term :- Body)) :- !,
    translate_term(Term1, Term).
term_expansion((Term1 --> Body), (Term --> Body)) :- !,
    translate_term(Term1, Term).
term_expansion(Term1, Term) :-
    translate_term(Term1, Term).
