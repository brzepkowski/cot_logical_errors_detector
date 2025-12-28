:- discontiguous step/3.
:- discontiguous step/4.
:- discontiguous rule/4.
:- discontiguous normalize/2.

% -------------------------
% Steps (the CoT trace)
% -------------------------

step(1, given, apples_total(10)).
step(2, given, apples_eaten(3)).

step(3, inference, rule_remaining_apples, apples_remaining(7)).
rule(rule_remaining_apples, subtraction_rule, [apples_total(_), apples_eaten(_)], apples_remaining(_)).
normalize(apples_total(X), minuend(X)).
normalize(apples_eaten(Y), subtrahend(Y)).
normalize(apples_remaining(Z), difference(Z)).

step(4, given, apples_new(8)).

step(5, inference, rule_new_apples, apples_final(15)).
rule(rule_new_apples, addition_rule, [apples_remaining(_), apples_new(_)], apples_final(_)).
normalize(apples_remaining(X), addend_0(X)).
normalize(apples_new(Y), addend_1(Y)).
normalize(apples_final(Z), sum(Z)).

% -------------------------
% Derivability
% -------------------------

available(Fact, Step) :-
    step(S, inference, RuleName, Fact),
    S < Step,
    rule(RuleName, _, Premises, Fact),
    forall(member(P, Premises), available(P, S)).

available(Fact, Step) :-
    step(S, given, Fact),
    S < Step.

% -------------------------
% Correctness
% -------------------------

:- use_module(library(clpfd)).

valid_schema(subtraction_rule,
    [minuend(X), subtrahend(Y)],
    difference(Z)) :-
    Z #= X - Y.

valid_schema(addition_rule,
    [addend_0(X), addend_1(Y)],
    sum(Z)) :-
    Z #= X + Y.

% valid_schema(multiplication_rule,
%     [count(N), value(V)],
%     total(T)) :-
%     T #= N * V.

% valid_schema(average_rule,
%     [sum(S), count(N)],
%     average(A)) :-
%     N #> 0,
%     A * N #= S.

% -------------------------
% Validators
% -------------------------

valid_rule(RuleName, Premises, Conclusion) :-
    rule(RuleName, Schema, Premises, Conclusion),
    maplist(normalize, Premises, NormPremises),
    normalize(Conclusion, NormConclusion),
    valid_schema(Schema, NormPremises, NormConclusion).

% Below bind_premises() tries to match each premise (required input) with an actual available fact,
% ensuring that all the premises needed for a rule can be "filled in" with real data.
bind_premises([], _).
bind_premises([P|Ps], StepID) :-  % split Premises into first premise `P` and remaining premises `Ps`
    available(Fact, StepID),  % search for any Fact available at StepID
    Fact = P,  % try to unify Fact with P
    bind_premises(Ps, StepID).

valid_step(StepID) :-
    step(StepID, inference, RuleName, StepConclusion),
    rule(RuleName, _, Premises, RuleConclusion),
    StepConclusion = RuleConclusion,
    bind_premises(Premises, StepID),
    valid_rule(RuleName, Premises, StepConclusion),
    forall(member(P, Premises), available(P, StepID)).

valid_conclusion(StepID) :-
    step(StepID, conclusion, Fact),
    available(Fact, StepID).

% -------------------------
% Audit the entire CoT
% -------------------------

audit :-
    forall(step(S, inference, _ , _), valid_step(S)),
    forall(step(S, conclusion, _), valid_conclusion(S)).
