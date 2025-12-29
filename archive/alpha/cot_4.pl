% --------------------------
% Example CoT
% --------------------------
% Given facts
page_count(25).
frames_per_page_average(280).

% Inference steps
step(1, given, page_count(25)).
step(2, given, frames_per_page_average(280)).
step(3, inference, frames_per_page(305, 10)).
step(4, inference, frames_per_page(250, 7)).
step(5, inference, remaining_pages(8)).
step(6, inference, frames_per_page_average(280, 8)).
step(7, inference, total_frames(3050, 10)).
step(8, inference, total_frames(1750, 7)).
step(9, inference, total_frames(2240, 8)).
step(10, inference, total_frames(7040)).

% Rules
rule(frames_per_page(Frames, Pages), [page_count(Pages)], frames_per_page_average(Frames, Pages)).
rule(remaining_pages(Remaining), [page_count(25), frames_per_page(305, 10), frames_per_page(250, 7)], Remaining).
rule(frames_per_page_average(Frames, Pages), [frames_per_page(Frames, Pages)], frames_per_page_average(Frames)).
rule(total_frames(Frames), [frames_per_page(3050, 10), frames_per_page(1750, 7), frames_per_page(2240, 8)], Frames).

% Conclusion
step(11, conclusion, total_frames(7040)).

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
