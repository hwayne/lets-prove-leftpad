:- use_module(library(clpfd)).

all_equal([], _).
all_equal([C|T], C) :- all_equal(T, C).

leftpad(C, N, Str, Padded) :-
    % Check the length requirement
    length(Str, L),
    NewL #= max(L, N),
    length(Padded, NewL),

    % The suffix is Str
    append(Prefix, Str, Padded),

    % The prefix is all C
    all_equal(Prefix, C).

