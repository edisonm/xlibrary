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

:- module(limit_order_by,
          [ limit_order_by/3 % +Count, +Spec, :Goal
          ]).

:- use_module(library(lists)).
:- use_module(library(solution_sequences)).

%!   limit_order_by(+Count, +Spec, :Goal)
%
%    Optimized version that combines limit/2 and order_by/3 in one predicate.
%    It avoids to keep all the solutions in memory, but only Count instead.
%    It is equivalent to:
%
%    limit_order_by(Count, Spec, Goal) :- limit(Count, order_by([Spec], Goal)).

compare(asc,  Order, Term1, Term2) :- compare(Order, Term2, Term1).
compare(desc, Order, Term1, Term2) :- compare(Order, Term1, Term2).

spec_sort(Dir, L1, L2) :-
    predsort(compare(Dir), L1, L2).

dir_key(asc( Key), asc,  Key).
dir_key(desc(Key), desc, Key).

inv_order(asc, desc).
inv_order(desc, asc).

:- meta_predicate limit_order_by(+, ?, 0).

limit_order_by(Count, Spec, Goal) :-
    SHolder = s([]),
    term_variables(Goal, Vars),
    dir_key(Spec, Dir, Key),
    forall(call_nth(Goal, N),
           (   SHolder = s(L1),
               (   N =< Count
               ->  nb_setarg(1, SHolder, [Key-Vars|L1])
               ;   spec_sort(Dir, [Key-Vars|L1], [_|L]),
                   nb_setarg(1, SHolder, L)
               )
           )),
    SHolder = s(KeyVarsU),
    inv_order(Dir, Inv),
    spec_sort(Inv, KeyVarsU, KeyVarsL),
    member(Key-Vars, KeyVarsL).
