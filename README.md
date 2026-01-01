# CoT logical errors detector

# 1. Input math problem

To test the pipeline I used the following example from the [NuminaMath database](https://huggingface.co/datasets/AI-MO/NuminaMath-CoT/viewer/default/train?views%5B%5D=train&row=6):

**Problem statement:**
```
Julian is writing a comic book. On average, his story has 280 frames per page. In his 25-page book, 10 pages have 305 frames, 7 pages have 250 frames, and the remaining pages have the average number of frames. How many frames will there be in total in his comic book?
```

**Correct CoT:**
```
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

So, there will be a total of $\boxed{7040}$ frames in Julian's comic book.
```

# 2. Repo structure:
- `prompt_0.py` - defines prompts used in the conversion step in the first two experiments: correct reasoning, and reasoning with a missing step.
- `prompt_1.py` - defines prompts used in the conversion step in the third experiment with the incorrect math.
- `cot_claude_correct.pl` - result of converion of the correct CoT using Claude Sonnet-4.5.
- `cot_claude_missing_step.pl` - result of converion of the CoT with missing reasoning step using Claude Sonnet-4.5.
- `cot_openai_wrong_calculation.pl` - result of converion of the CoT with incorrect math using GPT-5.2.

# 3. Running the code

**Experiment 1 - correct CoT:**
```
$ swipl -s ./cot_claude_correct.pl -g "audit, halt"

✓ Step 3 (inference) is valid
✓ Step 6 (inference) is valid
✓ Step 8 (inference) is valid
✓ Step 9 (inference) is valid
✓ Step 11 (inference) is valid
✓ Step 12 (inference) is valid
✓ Step 13 (inference) is valid
```

**Experiment 2 - CoT with missing step:**
```
$ swipl -s ./cot_claude_missing_step.pl -g "audit, halt"

✓ Step 3 (inference) is valid
✓ Step 6 (inference) is valid
✗ Step 9 (inference) FAILED
```

**Experiment 3 - CoT with wrong math:**
```
$ swipl -s ./cot_openai_wrong_calculation.pl -g "audit, halt"

✓ Step 5 (inference) is valid
✓ Step 8 (inference) is valid
✓ Step 9 (inference) is valid
✗ Step 10 (inference) FAILED
```