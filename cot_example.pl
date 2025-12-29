:- discontiguous step/3.
:- discontiguous step/4.
:- discontiguous rule/4.
:- discontiguous normalize/2.

% -------------------------
% Steps (the CoT trace)
% -------------------------

step(1, given, apples_joey(10)).
step(2, given, apples_joey_eaten(3)).

step(3, inference, rule_joey_eaten_apples, apples_joey_remaining(7)).
rule(rule_joey_eaten_apples, subtraction_rule, [apples_joey(_), apples_joey_eaten(_)], apples_joey_remaining(_)).
normalize(apples_joey(X), minuend(X)).
normalize(apples_joey_eaten(Y), subtrahend(Y)).
normalize(apples_joey_remaining(Z), difference(Z)).

step(4, given, apples_chandler(8)).

step(5, inference, rule_chandler_new_apples, apples_daily(15)).
rule(rule_chandler_new_apples, addition_rule, [apples_joey_remaining(_), apples_chandler(_)], apples_daily(_)).
normalize(apples_joey_remaining(X), addend_0(X)).
normalize(apples_chandler(Y), addend_1(Y)).
normalize(apples_daily(Z), sum(Z)).

step(6, given, days_in_week(7)).

step(7, inference, rule_weekly_apples, apples_weekly(104)).
rule(rule_weekly_apples, multiplication_rule, [apples_daily(_), days_in_week(_)], apples_weekly(_)).
normalize(apples_daily(X), factor_0(X)).
normalize(days_in_week(Y), factor_1(Y)).
normalize(apples_weekly(Z), product(Z)).

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

valid_schema(multiplication_rule,
    [factor_0(X), factor_1(Y)],
    product(Z)) :-
    Z #= X * Y.

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

% valid_conclusion(StepID) :-
%     step(StepID, conclusion, Fact),
%     available(Fact, StepID).

% -------------------------
% Audit the entire CoT
% -------------------------

% audit :-
%     forall(step(S, inference, _ , _), valid_step(S)),
%     forall(step(S, conclusion, _), valid_conclusion(S)).

% audit :-
%     forall(
%         step(S, inference, _, _),
%         (valid_step(S) -> 
%             format('✓ Step ~w (inference) is valid~n', [S])
%         ;
%             format('✗ Step ~w (inference) FAILED~n', [S]),
%             fail
%         )
%     ),
%     forall(
%         step(S, conclusion, _),
%         (valid_conclusion(S) ->
%             format('✓ Step ~w (conclusion) is valid~n', [S])
%         ;
%             format('✗ Step ~w (conclusion) FAILED~n', [S]),
%             fail
%         )
%     ).

audit :-
    forall(
        step(S, inference, _, _),
        (valid_step(S) -> 
            format('✓ Step ~w (inference) is valid~n', [S])
        ;
            format('✗ Step ~w (inference) FAILED~n', [S]),
            fail
        )
    ).
