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

:- module(execute_goal,
          [ execute_goal/2
          ]).

:- use_module(library(heaps)).
:- use_module(library(assoc)).
:- use_module(library(option)).

/*
Opts:
  - limit(N)                        mandatory
  - order_by(asc(Key) | desc(Key))  Optional, Key is a term evaluated in Goal's context
  - distinct(W)                     term; skip solutions that bounds W to the same value.
                                    If not provided the original order is preserved
  - group_by(G)                     optional term; if given, do top-K per group, if not
                                    provided, it equates to put all in one single group

semantically equivalent to:
    group_by(G, Goal, limit(N, distinct(W, order_by(OrderSpec, Goal))), GKGoalL),
    member(GK-GoalL, GKGoalL),
    member(Goal, GoalL).

- Note that the chosen order of operations is not casual.

- Performs better in terms of memory consumption.

*/

% Test:

% ?- findall(X-Y, execute_goal([limit(3),distinct(Y),order_by(asc(X))], member(X-Y, [6-z,3-a,2-a,1-a,3-b,4-c,5-d])), L).
% L = [1-a, 3-b, 4-c].

% To compare performance wrt library(solution_sequences):

% whoo:
% ?- findall(E, between(1,1000,E),L),findall(E1-E2, limit(10, distinct(E1-E2, order_by([asc(E2)], ( append(_, [E1|T], L), member(E2, T) )))),L2),length(L2,S2).
% ERROR: Stack limit (1.0Gb) exceeded

% whee:
% ?- time((findall(E, between(1,1000,E),L),findall(E1-E2, execute_goal([limit(10),distinct(E1-E2),order(asc(E2))],( append(_, [E1|T], L), member(E2, T) )), L2), length(L2, S2))).
% % 21,981,983 inferences, 0.825 CPU in 0.825 seconds (100% CPU, 26650647 Lips)
% ...

:- meta_predicate execute_goal(+, 0).

execute_goal(Opts, Goal) :-
    option(limit(Count), Opts, inf),
    option(order_by(OrderSpec), Opts, asc(unordered)),
    option(group_by(Group), Opts, ungrouped),
    (   option(distinct(Witness), Opts)
    ->  Distinct = true
    ;   Distinct = false
    ),
    priority_for(OrderSpec, Pri, Key),
    execute_goal(Goal, Count, Pri, Key, Distinct, Witness, Group).

/* ---------- ordering ---------- */

% We store entries with a "priority" such that the heap root is the WORST
% among kept ones. Then replacement is cheap.
%
% For asc(Key): "best" = smallest Key. "worst" = largest Key.
% So make heap a max-heap on Key by using priority = Key and using a max-heap?
% library(heaps) is a min-heap, so emulate max-heap by negating an order key
% or by wrapping with a reversed term order.
%
% Easiest: map Key to Priority so that worse == smaller Priority (min-heap root).
% For asc: worse = larger Key, so Priority = key_rank(Key) where larger Key => smaller Priority
% We can use Priority = rev(Key) where rev/1 compares reverse via standard order.

priority_for(asc(Key),  @=<, Key).
priority_for(desc(Key), @>=, Key).

% Because root is WORST, a candidate is "better" if its priority is GREATER
% than worst priority (min-heap root means smallest = worst).
better_than(@>=, P1, P2) :- P1 @> P2.
better_than(@=<, P1, P2) :- P1 @< P2.

setup_state(false, none).
setup_state(true,  state(DictHolder)) :-
    empty_assoc(D0),
    DictHolder = holder(D0).

seen_hash(state(holder(D)), Hash, Key) :-
    get_assoc(Hash, D, Key).

mark_hash(state(DictHolder), Hash, Key) :-
    DictHolder = holder(D0),
    put_assoc(Hash, D0, Key, D1),
    nb_setarg(1, DictHolder, D1),
    true.

update_topk(Count, Pri, Key, Entry, HHolder) :-
    HHolder = holder(N0, H0),
    (   N0 < Count
    ->  add_to_heap(H0, Key, Entry, H1),
        N1 is N0 + 1,
        nb_setarg(1, HHolder, N1),
        nb_setarg(2, HHolder, H1)
    ;   % Heap full: compare with worst (root because root is "worst")
        replace_topk(_WorstKey, Pri, Key, Entry, HHolder)
    ).

revdel_from_heap(Q0,Px,X,Q) :-
    get_from_heap(Q0,Py,Y,Q1),
    revdel_from_heap(Q1,Px,X,Q2),
    add_to_heap(Q2,Py,Y,Q),
    !.
revdel_from_heap(Q0,P,X,Q) :-
    get_from_heap(Q0,P,X,Q).

pri_del_from_heap(Pri, H0, Key, Entry, HRest) :-
    (   var(Key),
        Pri == (@=<)
    ->  revdel_from_heap(H0, Key, Entry, HRest)
    ;   delete_from_heap(H0, Key, Entry, HRest)
    ).

replace_topk(Key1, Pri, Key, Entry, HHolder) :-
    HHolder = holder(_, H0),
    pri_del_from_heap(Pri, H0, Key1, _, HRest),
    (   better_than(Pri, Key, Key1)
    ->  add_to_heap(HRest, Key, Entry, H1),
        nb_setarg(2, HHolder, H1)
    ;   fail
    ).

heap_to_list(holder(_N, H), Pri, SortedKeyVars) :-
    heap_to_list(H, KV0),
    sort(1, Pri, KV0, SortedKeyVars).

/* ---------- grouped execution (top-K per group) ---------- */

execute_goal(Goal, Count, Pri, Key, Distinct, Witness, Group) :-
    term_variables(Goal, Vars),
    setup_state(Distinct, State),
    empty_assoc(G0),
    GHolder = holder(G0),  % maps GroupKey -> holder(N,Heap)
    term_variables(Witness, WVars),
    WTerm =.. [w|WVars],
    forall(Goal,
           ignore(consider_solution(Count, Pri, Key, Distinct, WTerm, Group, Vars, State, GHolder))),
    finalize(Pri, GHolder, Vars).

consider_solution(Count, Pri, Key, Distinct, WTerm, Group, Vars, State, GHolder) :-
    Entry = Vars,
    ( Distinct == true
    ->variant_sha1(WTerm, Hash),
      ( seen_hash(State, Hash, Key1)
      ->get_or_create_bucket(GHolder, Group, Bucket),
        replace_topk(Key1, Pri, Key, Entry, Bucket),
        GHolder = holder(G0),
        put_assoc(Group, G0, Bucket, G1),
        nb_setarg(1, GHolder, G1),
        mark_hash(State, Hash, Key),
        fail
      ; true
      )
    ; true
    ),
    get_or_create_bucket(GHolder, Group, Bucket),
    update_topk(Count, Pri, Key, Entry, Bucket),
    GHolder = holder(G0),
    put_assoc(Group, G0, Bucket, G1),
    nb_setarg(1, GHolder, G1),
    mark_hash(State, Hash, Key).

get_or_create_bucket(GHolder, Group, Bucket) :-
    GHolder = holder(G0),
    (   get_assoc(Group, G0, Bucket)
    ->  true
    ;   empty_heap(H0),
        Bucket = holder(0, H0),
        put_assoc(Group, G0, Bucket, G1),
        nb_setarg(1, GHolder, G1)
    ).

finalize(Pri, holder(G), Vars) :-
    gen_assoc(_GK, G, Bucket),
    heap_to_list(Bucket, Pri, List),
    member(_Key-Vars, List).
