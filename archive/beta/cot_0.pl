% -------------------------
% Steps (the CoT trace)
% -------------------------

step(1, given, apples_total(10)).
step(2, given, apples_eaten(3)).

step(3, inference, rule_remaining_apples).

step(4, conclusion, apples_remaining(7)).


% -------------------------
% Rule structure
% -------------------------

rule(rule_remaining_apples,
     [apples_total(T), apples_eaten(E)],
     apples_remaining(R)).

% -------------------------
% Derivability
% -------------------------

available(Fact, Step) :-
    step(S, inference, RuleName),
    S < Step,
    rule(RuleName, Premises, Fact),
    forall(member(P, Premises), available(P, S)).

available(Fact, Step) :-
    step(S, given, Fact),
    S < Step.

% -------------------------
% Correctness (semantic validation)
% -------------------------

:- use_module(library(clpfd)).

valid_rule(rule_remaining_apples,
    [apples_total(T), apples_eaten(E)],
    apples_remaining(R)) :-
    T #>= 0,
    E #>= 0,
    R #>= 0,
    R #= T - E.

% -------------------------
% Step validation
% -------------------------

valid_step(StepID) :-
    step(StepID, inference, RuleName),
    rule(RuleName, Premises, Conclusion),
    valid_rule(RuleName, Premises, Conclusion),
    forall(member(P, Premises), available(P, StepID)).

% -------------------------
% Audit the entire CoT
% -------------------------

audit :-
    forall(step(S, inference, _), valid_step(S)).
