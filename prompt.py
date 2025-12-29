def prompt(problem, cot):

    return f"""
You are a program that converts a natural language chain-of-thought (CoT) into fully executable Prolog code.

The output should include:
1. A list of steps (facts and inference steps).
2. For facts use the following template:
```
step(StepId, given, Fact).
```
3. For inference steps use the following template:
```
step(StepId, inference, RuleName, Result(Value)).
rule(RuleName, RuleSchema, [Premise_0(_), Premise_1(_), ..., Premise_N(_)], Result(_)).
normalize(Premise_0(X_0), ArgName_0(X_0)).
normalize(Premise_1(X_1), ArgName_1(X_1)).
...
normalize(Premise_N(X_N), ArgName_N(X_N)).
normalize(Result(Y), SchemaResult(Y)).
```
4. For RuleSchemas use the following schemas:
```
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
```
5. If you need a RuleSchame, which is not present in the above code snippet, create a new Schema and add it at the end of the generated code.

-----------------
EXAMPLE

INPUT PROBLEM:
Joey and Chandler live together.
Joey bought 10 apples. He came back home and ate 3 of them.
Then Chandler came back home with 8 new apples.
The same story repeated for 7 days.
How many apples the two frineds have after seven days?

INPUT CoT:
<think>

To determine the total number of apples Joey and Chandler have after seven days, I'll start by analyzing the events that occur each day.

Every day, Joey buys 10 apples and eats 3, leaving him with 7 apples. Chandler then brings 8 new apples to their home. Combining these, they have 7 + 8 = 15 apples each day.

Over the course of 7 days, this daily total accumulates. Multiplying the daily total by the number of days gives 15 apples/day * 7 days = 105 apples.

Therefore, after seven days, Joey and Chandler together have 105 apples.
</think>

OUTPUT:
```
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
```

-----------------
Now conduct analogous conversion for the following problem and CoT.
INPUT PROBLEM:
{problem}

INPUT CoT:
<think>
{cot}
</think>
    """

if __name__ == "__main__":
    problem = r"""
Julian is writing a comic book. On average, his story has 280 frames per page. In his 25-page book, 10 pages have 305 frames, 7 pages have 250 frames, and the remaining pages have the average number of frames. How many frames will there be in total in his comic book?
    """

    cot = r"""
First, let's calculate the total number of frames for the pages that don't have the average number of frames.

For the 10 pages with 305 frames each:
10 pages * 305 frames/page = 3050 frames

For the 7 pages with 250 frames each:
7 pages * 250 frames/page = 1750 frames

Now, let's find out how many pages have the average number of frames. Julian's book has 25 pages in total, and we already know the frame count for 17 of them (10 with 305 frames and 7 with 250 frames).

25 pages - 10 pages - 7 pages = 8 pages

These 8 pages have the average number of frames, which is 280 frames per page.

8 pages * 280 frames/page = 2240 frames

Now, let's add up all the frames:

3050 frames (from the 10 pages) + 1750 frames (from the 7 pages) + 2240 frames (from the 8 pages) = 7040 frames

So, there will be a total of $\boxed{7040}$  frames in Julian's comic book.
    """

    print(prompt(problem, cot))