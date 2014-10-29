:- module(i18n_parser, [parse_po_entry/3, parse_po_entries/3]).

tr_text(A,B,T) :- append(A,T,B).

comment(Text) --> "#", tr_text(Text), "\n".

translator_comments([TC|TCs]) -->
	"# ", tr_text(TC), "\n",
	!,
	translator_comments(TCs).
translator_comments([[]|TCs]) -->
	"#\n",
	!,
	translator_comments(TCs).
translator_comments([]) --> [].

extracted_comments([EC|ECs]) -->
	"#. ", tr_text(EC), "\n",
	!,
	extracted_comments(ECs).
extracted_comments([]) --> [].

reference([R|Rs]) -->
	"#: ", tr_text(R), "\n",
	!,
	reference(Rs).
reference([]) --> [].

flag([F|Fs]) -->
	"#, ", tr_text(F), "\n",
	!,
	flag(Fs).
flag([]) --> [].

%% parse_po_entries(+Term,-Codes,?Tail).
%% parse_po_entries(-Term,+Codes,?Tail).

%% Note that parse_po_entries/3 is reversible, it is used to compile and
%% to decompile the .po file. Example:

/*
%% i18n_support:parse_po_entries([i18n_support:i18n("a","b","c"),
%% i18n_support:i18n("a","b\nc","c")],D,[]), atom_codes(A,D),write(A).

  read_file_to_codes('/usr/share/cups/locale/es/cups_es.po',C,[]),
  i18n_support:parse_po_entries(Term,C,[]),
  i18n_support:parse_po_entries(Term,S,[]),format('~s',[S]).
*/

parse_po_entry(entry(TranslatorComments, ExtractedComments,
		     Reference, Flag, MsgId, MsgStr)) -->
	translator_comments(TranslatorComments),
	extracted_comments(ExtractedComments),
	reference(Reference),
	flag(Flag),
	msg("msgid", MsgId),
	msg("msgstr", MsgStr),
	( "\n" ->[] ; [] ),
	!.
parse_po_entry(comment(Text)) -->
	comment(Text).
parse_po_entry(nl) -->
	"\n".
% parse_po_entry(error(E)) --> flush(E).

% flush([E|T]) --> [E], !, flush(T).
% flush([]) --> [].

parse_po_entries([Entry|Tail]) -->
	parse_po_entry(Entry),
	!,
	parse_po_entries(Tail).
parse_po_entries([]) --> [].

msg(Key, [Line|Lines]) -->
	phrase(Key), " ",
	text_line(Line),
	text_lines(Lines), !.

text_lines([Line|Lines]) --> text_line(Line), text_lines(Lines).
text_lines([]) --> "".

text_line(Line) --> "\"", escape_text(Line), "\"\n".

escape_char(0'\n) --> "\\n", !.
escape_char(0'\") --> "\\\"", !.
escape_char(0'\\) --> "\\\\", !.
escape_char(C) --> [C].

escape_text([]) --> [].
escape_text([C|Text]) --> escape_char(C), escape_text(Text).