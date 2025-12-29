from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig
from typing import List
import torch
import json
import pandas as pd

# ----- Load the example CoT -----
df = pd.read_parquet("numina_math_cot_sample.parquet")
df = df[df["source"] == "orca_math"]

data = df[["problem", "solution"]].to_dict('records')

problem = data[0]["problem"]
cot = data[0]["solution"]

# ----- Create prompt -----
prompt = f"""
You are a program that converts a natural language chain-of-thought (CoT) into fully executable Prolog code.
Output two things:
1. A list of steps (facts and inference steps), using step(ID, given|inference|conclusion, FactOrRule).
2. A list of rules, using rule(name, [Premises], Conclusion).

Example format:

step(1, given, value(a,2)).
step(2, inference, rule1).
rule(rule1, [value(a,2)], value(b,4)).
step(3, inference, rule2).
rule(rule2, [value(b,4)], value(c,5)).
step(4, conclusion, value(c,5)).

Now convert this CoT into that format:
{problem}
<think>
{cot}
</think>
"""

print(f"prompt:\n{prompt}")

import sys
sys.exit()

# ----- Load the model -----
# checkpoint = "deepseek-ai/deepseek-coder-7b-instruct-v1.5"
checkpoint = "deepseek-ai/DeepSeek-R1-Distill-Qwen-7B"

bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_compute_dtype=torch.float16,
    bnb_4bit_use_double_quant=True,
    bnb_4bit_quant_type="nf4",
)

tokenizer = AutoTokenizer.from_pretrained(checkpoint)
tokenizer.pad_token = tokenizer.eos_token

model = AutoModelForCausalLM.from_pretrained(
    checkpoint,
    quantization_config=bnb_config,
    device_map="auto",
)

messages=[
    { 'role': 'user', 'content': prompt}
]
inputs = tokenizer.apply_chat_template(
    messages,
    add_generation_prompt=True,
    return_tensors="pt",
    padding=True,
    return_attention_mask=True
).to(model.device)

outputs = model.generate(
    inputs,
    max_new_tokens=2000,
    do_sample=False,
    top_k=50,
    num_return_sequences=1,
    eos_token_id=tokenizer.eos_token_id,
    pad_token_id=tokenizer.pad_token_id,
)
llm_answer = tokenizer.decode(outputs[0][len(inputs[0]):], skip_special_tokens=True)

print("llm_answer: ", llm_answer)
 