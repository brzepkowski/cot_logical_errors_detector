% --------------------------
% Example CoT
% --------------------------
step(1, given, page_count(10, 305)).
step(2, given, page_count(7, 250)).
step(3, given, total_pages(25)).
step(4, inference, subtract_page_counts).
step(5, inference, calculate_average_frames).
step(6, inference, calculate_total_frames).
step(7, conclusion, total_frames(7040)).

rule(subtract_page_counts, [page_count(10, 305), page_count(7, 250), total_pages(25)], page_count(8, 280)).
rule(calculate_average_frames, [page_count(8, 280)], average_frames(280)).
rule(calculate_total_frames, [page_count(10, 305), page_count(7, 250), page_count(8, 280)], total_frames(3050 + 1750 + 2240)).

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
