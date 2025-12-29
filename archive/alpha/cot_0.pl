% Example CoT:
% Given a = 2.
% If a = 2 then b = 4.
% If b = 4 then c = 5.
% Therefore c = 5.

% --- steps ---
step(1, given, value(a,2)).
step(2, inference, rule1).  % If a = 2 then b = 4.
step(3, inference, rule2).  % If b = 4 then c = 5.
step(4, conclusion, value(c,5)). % Therefore c = 5.

% --- declared rules ---
rule(rule1, [value(a,2)], value(b,4)).
rule(rule2, [value(b,4)], value(c,5)).

available(Fact, Step) :-
    step(S, inference, RuleName),
    S < Step,
    rule(RuleName, Premises, Fact),
    forall(member(P, Premises), available(P, S)).
available(Fact, Step) :-
    step(S, given, Fact),
    S < Step.

