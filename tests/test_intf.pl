:- module(test_intf,
          [intf_pred/3,
           intf_meta/2]).

:- use_module(library(interface)).
:- init_expansors.

:- interface.

:- meta_predicate intf_meta(0,+).
