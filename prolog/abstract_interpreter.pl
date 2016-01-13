/*  Part of Extended libraries for Prolog

    Author:        Edison Mera Menendez
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/refactor, http://www.swi-prolog.org
    Copyright (C): 2015, Process Design Center, Breda, The Netherlands.

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

:- module(abstract_interpreter, [abstract_interpreter/2,
				 abstract_interpreter/4,
				 match_head/7,
				 match_head_body/3,
				 bottom/2,
				 match_ai/8,
				 match_noloops/7,
				 terms_share/2]).

:- use_module(xlibrary(implementation_module)).
:- use_module(xlibrary(qualify_meta_goal)).
:- use_module(xlibrary(resolve_calln)).
:- use_module(xtools(extra_location)).
:- use_module(xtools(term_size)).

:- meta_predicate
    match_head_body(*,*,*),
    match_ai(*,*,*,*,*,*,*,*),
    match_noloops(*,*,*,*,*,*,*),
    abstract_interpreter(+,+,7,-),
    abstract_interpreter(?,7).

abstract_interpreter(Goal, M, Abstraction, data(0, [], Result)) :-
    ( abstract_interpreter(Goal, M, Abstraction, [], [], Result)
    *->true
    ; Result = fail
    ).

/*
:- meta_predicate catch(2, ?, ?, ?, ?).
catch(DCG, Ex, H, S0, S) :-
    catch(call(DCG, S0, S), Ex, H).

cut_to(Goal) --> catch(Goal, cut_from, true).

cut_from.
cut_from :- throw(cut_from).
*/

% alternative (and more efficient) implementation follows:
:- use_module(xlibrary(intercept)).

:- meta_predicate intercept(2, ?, ?, ?, ?).
intercept(DCG, Ex, H, S0, S) :-
    intercept(call(DCG, S0, S), Ex, H).

cut_to(Goal) -->
    {prolog_current_choice(CP)},
    intercept(Goal, cut_from, prolog_cut_to(CP)).

cut_from :- send_signal(cut_from).

abstract_interpreter(M:Goal, Abstraction) :-
    cut_to(abstract_interpreter_body(Goal, M, Abstraction, []), [], _).

abstract_interpreter_body(Goal, M, _, _) -->
    {var(Goal) ; var(M)}, bottom, !.
abstract_interpreter_body(M:Goal, _, Abs, State) --> !,
    abstract_interpreter_body(Goal, M, Abs, State).
abstract_interpreter_body(call(Goal), M, Abs, State) --> !,
    cut_to(abstract_interpreter_body(Goal, M, Abs, State)).
abstract_interpreter_body(CallN, M, Abs, State) -->
    {do_resolve_calln(CallN, Goal)}, !,
    cut_to(abstract_interpreter_body(Goal, M, Abs, State)).
abstract_interpreter_body(\+ A, M, Abs, State) --> !,
    \+ cut_to(abstract_interpreter_body(A, M, Abs, State)).
abstract_interpreter_body(once(Goal), M, Abs, State, S0, S) :- !,
    once(abstract_interpreter_body(Goal, M, Abs, State, S0, S)).
abstract_interpreter_body(setup_call_cleanup(S, C, E), M, Abs, State, S0, S) :- !,
    setup_call_cleanup(abstract_interpreter_body(S, M, Abs, State, S0, S1),
		       abstract_interpreter_body(C, M, Abs, State, S1, S2),
		       abstract_interpreter_body(E, M, Abs, State, S2, S)).
abstract_interpreter_body(call_cleanup(C, E), M, Abs, State, S0, S) :- !,
    call_cleanup(abstract_interpreter_body(C, M, Abs, State, S0, S1),
		 abstract_interpreter_body(E, M, Abs, State, S1, S)).
abstract_interpreter_body((A, B), M, Abs, State) --> !,
    { \+ terms_share(A, B)
    ->CutOnFail = true
    ; CutOnFail = fail
    },
    abstract_interpreter_body(A, M, Abs, State),
    ( abstract_interpreter_body(B, M, Abs, State)
    *->[]
    ; { CutOnFail == true
      ->!, fail			% The whole body will fail
      }
    ).
abstract_interpreter_body((A;B), M, Abs, State) --> !,
    ( abstract_interpreter_body(A, M, Abs, State)
    ; abstract_interpreter_body(B, M, Abs, State)
    ).
abstract_interpreter_body(A->B, M, Abs, State) --> !,
    { \+ terms_share(A, B)
    ->CutOnFail = true
    ; CutOnFail = fail
    },
    cut_to(abstract_interpreter_body(A, M, Abs, State)), % loose of precision
    ( \+ is_bottom
    ->!
    ; []
    ),
    ( abstract_interpreter_body(B, M, Abs, State)
    *->[]
    ; { CutOnFail == true
      ->!, fail
      }
    ).
abstract_interpreter_body(!, _, _, _) --> cut_if_no_bottom.
abstract_interpreter_body(A=B, _, _, _) --> !, {A=B}.
abstract_interpreter_body(true, _, _, _) --> !.
abstract_interpreter_body(fail, _, _, _) --> !, {fail}.
abstract_interpreter_body(H, M, Abs, State) -->
    cut_to(abstract_interpreter(H, M, Abs, State)).

terms_share(A, B) :-
    term_variables(A, VarsA),
    term_variables(B, VarsB),
    ( member(VA, VarsA),
      member(VB, VarsB),
      VA==VB
    ), !.

is_bottom(bottom, bottom).

cut_if_no_bottom -->
    (\+ is_bottom
    ->{cut_from}
    ; []
    ).

abstract_interpreter(H, M, Abs, State0 ) -->
    { predicate_property(M:H, meta_predicate(Meta))
    ->qualify_meta_goal(M:H, Meta, Goal)
    ; Goal = H
    },
    call(Abs, Goal, M, CM:Body, State0, State),
    abstract_interpreter_body(Body, CM, Abs, State).

% top: empty set
% bottom: I don't know, universe set.
% true: exact result

bottom(_, bottom).

:- multifile match_ai/8.

match_ai(head,    G, M, Body, S0, S) --> match_head(   G, M, Body, S0, S).
match_ai(noloops, G, M, Body, S0, S) --> match_noloops(G, M, Body, S0, S).

match_head(Goal, M, M:true, _, _) -->
    {predicate_property(M:Goal, interpreted)}, !,
    { match_head_body(Goal, M, Body)
    *->true
    ; fail
    },
    ( {Body = _:true}
    ->[]
    ; bottom %% loose of precision
    ).
match_head(_,    M, M:true, _, _) --> bottom.

match_head_body(Goal, M, CMBody) :-
    ( extra_clauses(Goal, M, CMBody)
    ; clause(M:Goal, Body, Ref),
      clause_property(Ref, module(CM)),
      CMBody = CM:Body
    ).

:- use_module(xlibrary(interface), []).

:- multifile extra_clauses/3.

extra_clauses(Goal, CM, CM:true) :-
    predicate_property(CM:Goal, dynamic),
    implementation_module(CM:Goal, M),
    loc_dynamic(Goal, M, dynamic(def, _, _), _).
extra_clauses(Goal, CM, I:Goal) :-
    implementation_module(CM:Goal, M),
    functor(Goal, F, A),
    ( interface:'$interface'(M, DIL, IIL),
      ( memberchk(F/A, DIL)
      ; memberchk(F/A, IIL)
      )
    ->interface:'$implementation'(I, M)
    ).

match_noloops(Goal, M, Body, S, [M:F/A-Size|S]) -->
    {predicate_property(M:Goal, interpreted)}, !,
    ( { functor(Goal, F, A),
	term_size(Goal, Size),
	\+ ( memberchk(M:F/A-Size1, S),
	     Size1=<Size
	   )
      }
    ->{ match_head_body(Goal, M, Body) },
      []
    ; bottom %% loose of precision
    ).
match_noloops(_,    M, M:true, S, S) --> bottom.
