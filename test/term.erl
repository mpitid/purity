
-module(term).

-compile(export_all).

%% Collection of tests focused on the handling of BIFs by termination analysis.

%< global [termination]

%% Such a function cannot be resolved statically.
%< a/3 >= p
a(M, F, As) ->
    apply(M, F, As).

%% Still not sure about the arity of the called function.
%< b/1 >= p
b(As) ->
    apply(erlang, abs, As).

%% This call to apply is translated to a direct call by the compiler,
%% hence the full resolution of the function.
%< c/0 p
c() ->
    apply(erlang, abs, [1]).

