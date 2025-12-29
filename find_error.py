import sys
import re

if __name__ == "__main__":
    llm_output_prolog_transformed_path = sys.argv[1]
    trace_path = sys.argv[2]

    with open(llm_output_prolog_transformed_path, "r") as file:
        llm_output_prolog_transformed = file.readlines()

    steps = {}
    for line in llm_output_prolog_transformed:
        if re.search(r'step\(\d+', line):
            step_idx = int(line.replace("step(", "").split(",")[0])
            steps[step_idx] = line.replace("\n", "")

    with open(trace_path, "r") as file:
        trace_lines = file.readlines()
    
    failed = False
    for trace_line in trace_lines:
        if "FAILED" in trace_line:
            failed = True
            break

    if failed:
        print("CoT failed at: ", trace_line.replace("\n", ""), "...")
        failed_step_idx = int(trace_line.replace("✗ Step ", "").split("(")[0])
        failed_step = steps[failed_step_idx]
        print(f"\nwhich corresponds to the following statement:\n\n{failed_step}")
    else:
        print("CoT valid")
