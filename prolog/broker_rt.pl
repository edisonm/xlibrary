/*  Part of Extended Libraries for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xlibrary
    Copyright (C): 2015, Process Design Center, Breda, The Netherlands.
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

:- module(broker_rt, [remote_call/2]).

:- use_module(library(http/websocket)).
:- use_module(library(broker)).

%  Note: remote call of meta predicates can not be supported, because the client
%  context module could be inexistent in the server.

/*
:- meta_predicate
    remote_call(0 ).

remote_call(MCall) :-
    predicate_property(MCall, implementation_module(M)),
    remote_call(Call, M).
*/

remote_call(Call, M) :-
    term_variables(Call, Vars),
    remote_call(Call, M, Vars).

remote_call(Call, Module, Vars) :-
    ( module_server(Module, URL),
      directory_file_path(URL, Module, Path),
      catch(http_open_websocket(Path, WS, []),
            error(socket_error(_, _), _),
            fail)
    ->setup_call_cleanup(
          ws_send(WS, prolog(b(Call, Vars))),
          remote_call_loop(WS, Vars),
          ws_close(WS, 1000, "bye"))
    ; Module:Call % fallback to local call
    ).

remote_call_loop(WS, Vars) :-
    repeat,
      ws_receive(WS, Reply, [format(prolog)]),
      ( Reply.opcode = close
      ->!,
        fail
      ; e(Vars, Ex) = Reply.data
      ->throw(Ex)
      ; b(Vars) = Reply.data
      ->!
      ; n(Vars) = Reply.data
      ; ws_send(WS, prolog(next)),
        fail
      ).