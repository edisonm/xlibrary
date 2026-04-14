/*  Part of Extended Libraries for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xlibrary
    Copyright (C): 2022, Process Design Center, Breda, The Netherlands.
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

:- module(raw_loader,
          [ raw_load/1,
            raw_load/2,
            raw_file/2,
            raw_file/3
          ]).

:- use_module(library(lists)).
:- use_module(library(option)).

:- meta_predicate
        raw_load(:),
        raw_load(:,:).

abolish_predicates(M:L) :-
    forall(member(PI, L), abolish(M:PI)).

%!  raw_load(:Alias, :PredicateIndicators) is det.
%
%   Like raw_load/1, but in addition calls compile_predicates/1 to compile those
%   predicates into static predicates. Alias can be a list of aliases, in such
%   case all the aliases are loaded as if they where concatenated

raw_load(Alias, PI) :-
    abolish_predicates(PI),
    do_raw_load(Alias),
    compile_predicates(PI).

%!  raw_load(:Alias) is det.
%
%   Reads a file containing terms and assert them into the prolog database.
%   This is used to speed up loading of files that only contains unestructured
%   facts, that does not requires the whole compiler machinery.  For big files
%   it loads faster that qlf files (the first time).

raw_load(M:Alias) :-
    forall(( current_predicate(M:F/A),
             functor(H, F, A),
             predicate_property(M:H, dynamic),
             \+ predicate_property(M:H, imported_from(_))
           ),
           abolish(M:H)),
    do_raw_load(M:Alias).

raw_file(Alias, File, Opts1) :-
    merge_options(Opts1, [extensions([raw, ''])], Opts),
    absolute_file_name(Alias, File, Opts).

raw_file(Alias, File) :- raw_file(Alias, File, []).

do_raw_load(M:Alias) :-
    ( prolog_load_context(source, Source)
    ->T = [relative_to(Source)]
    ; T = []
    ),
    do_raw_load(Alias, M, [access(exist)|T]).

do_raw_load([A|B], M, T) :-
    !,
    do_raw_load(A, M, T),
    do_raw_load(B, M, T).
do_raw_load([], _, _) :- !.
do_raw_load(Alias, M, T) :-
    raw_file(Alias, File, T),
    setup_call_cleanup(
        open(File, read, Stream),
        raw_load_loop(Stream, M),
        close(Stream)).

raw_load_loop(Stream, M) :-
    repeat,
      read_term(Stream, Term, []),
      ( Term == end_of_file
      ->true
      ; assertz(M:Term),
        fail
      ),
    !.
