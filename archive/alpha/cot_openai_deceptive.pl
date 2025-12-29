% --------------------------
% Example CoT
% --------------------------
% Steps
step(1, given, pages_total(25)).
step(2, given, average_frames_per_page(280)).
step(3, given, pages_with_frames(10,305)).
step(4, given, pages_with_frames(7,250)).

step(5, inference, rule_remaining_pages).
step(6, inference, rule_frames_305).
step(7, inference, rule_frames_250).
step(8, inference, rule_frames_average).
step(9, inference, rule_total_frames).

step(10, conclusion, total_frames(7040)).

% Rules
rule(rule_remaining_pages,
     [pages_total(25), pages_with_frames(10,305), pages_with_frames(7,250)],
     remaining_pages(9)).

rule(rule_frames_305,
     [pages_with_frames(10,305)],
     frames_from_305_pages(3050)).

rule(rule_frames_250,
     [pages_with_frames(7,250)],
     frames_from_250_pages(1750)).

rule(rule_frames_average,
     [remaining_pages(9), average_frames_per_page(280)],
     frames_from_average_pages(2240)).

rule(rule_total_frames,
     [frames_from_305_pages(3050),
      frames_from_250_pages(1750),
      frames_from_average_pages(2240)],
     total_frames(7040)).

% --------------------------
% available/2 predicate
% --------------------------
available(Fact, Step) :-
    step(S, inference, RuleName),
    S < Step,
    rule(RuleName, Premises, Fact),
    forall(member(P, Premises), available(P, S)).

available(Fact, Step) :-
    step(S, given, Fact),
    S < Step.

% --------------------------
% Metric 1: number of inference steps
% --------------------------
num_inference_steps(Count) :-
    findall(Step, step(Step, inference, _), Steps),
    length(Steps, Count).

% --------------------------
% Metric 2: number of given facts
% --------------------------
num_given_facts(Count) :-
    findall(Fact, step(_, given, Fact), Facts),
    length(Facts, Count).

% --------------------------
% Metric 3: number of inferred facts
% --------------------------
num_inferred_facts(Count) :-
    findall(Fact,
            (step(S, inference, _), available(Fact, S)),
            Facts),
    sort(Facts, UniqueFacts),
    length(UniqueFacts, Count).

% --------------------------
% Metric 4: step coverage
% fraction of steps that actually contribute to the final conclusion
% --------------------------
% steps_contributing_to(FinalFact, ContributingSteps) :-
%     findall(Step,
%             (step(Step, inference, _),
%              available(FinalFact, Step)),
%             Steps),
%     sort(Steps, ContributingSteps).

% step_coverage(FinalFact, Coverage) :-
%     findall(Step, step(Step, inference, _), AllSteps),
%     steps_contributing_to(FinalFact, Contributing),
%     length(AllSteps, Total),
%     length(Contributing, Used),
%     (Total > 0 -> Coverage is Used / Total ; Coverage = 0).

% --------------------------
% Metric 5: maximum derivation depth
% --------------------------
derivation_depth(Fact, Depth) :-
    step(Step, given, Fact),
    Step > 0,
    Depth = 0.

derivation_depth(Fact, Depth) :-
    step(S, inference, RuleName),
    rule(RuleName, Premises, Fact),
    S > 0,
    findall(D,
            (member(P, Premises),
             derivation_depth(P, D1),
             D is D1 + 1),
            Depths),
    max_list(Depths, Depth).

% --------------------------
% How to use
% --------------------------
% Check correctness of reasoning
% available(value(c,5),4)
% true

% ?- num_inference_steps(C).
% C = 2.

% ?- num_given_facts(C).
% C = 1.

% ?- num_inferred_facts(C).
% C = 2.

% ?- step_coverage(value(c,5), Cov).
% Cov = 1.0.

% ?- derivation_depth(value(c,5), D).
% D = 2.
