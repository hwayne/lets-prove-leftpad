:- use_module(library(lists)).
:- use_module(library(clpz)).

leftpad(Char, N, Ls0, Ls) :-
    % 1 ) The length of the output is max(N, len(Ls0))
    length(Ls0, L0),
    L #= max(N, L0),
    length(Ls, L),
    % 2 ) The prefix of the output is padding characters and nothing but padding characters
    % 3 ) The suffix of the output is the original string
    append(Prefix, Ls0, Ls),
    maplist(=(Char), Prefix).
