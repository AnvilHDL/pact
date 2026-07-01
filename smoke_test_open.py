import os
import re
import subprocess
from enum import Enum


EXAMPLE_DIR = os.path.join(os.path.dirname(__file__), "session_examples")
# test_positive_compat / test_negative_compat are reused: the open algorithm
# specializes to the closed one when every message is internal, so they must
# reproduce the closed results. open_phase_channel_params exercises genuine
# boundary messages and the incremental i1-i2_i3 residual composition.
FILES = [
    "test_positive_compat.anvil",
    "test_negative_compat.anvil",
    "open_phase_channel_params.anvil",
]
ERROR_DIR = os.path.join(os.path.dirname(__file__), "error_logs_open")
BASE_DIR = os.path.dirname(__file__)
EXAMPLES = [os.path.join(EXAMPLE_DIR, file) for file in FILES]


class Result(Enum):
    Compatible = 1
    Incompatible = 2
    Error = 3

    def __str__(self):
        if self == Result.Compatible:
            return "Compatible"
        elif self == Result.Incompatible:
            return "Incompatible"
        elif self == Result.Error:
            return "Error"


def error_handler(out_log, file_name):
    if not os.path.exists(ERROR_DIR):
        os.makedirs(ERROR_DIR)
    file_base_name = os.path.basename(file_name)
    error_file = os.path.join(ERROR_DIR, "error_" + file_base_name + ".log")
    os.rename(out_log, error_file)


def result_handler(out_log, file_name):
    # Matches "[Open] Pool p13 Compatibility: true" (the prefix is ignored by
    # re.search, which scans mid-line).
    results = {}
    with open(out_log, 'r') as f:
        for line in f:
            if "Compatibility: true" in line:
                match = re.search(r"Pool (\w+) Compatibility: true", line)
                if match:
                    results[match.group(1)] = Result.Compatible
            elif "Compatibility: false" in line:
                match = re.search(r"Pool (\w+) Compatibility: false", line)
                if match:
                    results[match.group(1)] = Result.Incompatible

    error_handler(out_log, file_name)
    return results


def run_compat(file):
    file_base = os.path.basename(file)
    print("Running OPEN compatibility check on file: " + file_base)
    compat_temp_log = os.path.join(EXAMPLE_DIR, "compat_open_temp.txt")
    relative_file = os.path.relpath(file, BASE_DIR)
    # dune exec anvil -- -debug-choice 4 session_examples/<file>
    command = ["dune", "exec", "anvil", "--", "-debug-choice", "4", relative_file]
    with open(compat_temp_log, 'w') as f:
        subprocess.run(command, stdout=f, stderr=subprocess.STDOUT, cwd=BASE_DIR)

    return result_handler(compat_temp_log, file)


def table_of_results(results):
    if not results:
        print("No pool results found.")
        return

    pool_width = max(len("Pool"), max(len(pool_name) for pool_name in results))
    result_width = max(len("Result"), max(len(str(result)) for result in results.values()))

    separator = "+" + "-" * (pool_width + 2) + "+" + "-" * (result_width + 2) + "+"
    print(separator)
    print("| " + "Pool".ljust(pool_width) + " | " + "Result".ljust(result_width) + " |")
    print(separator)
    for pool_name in sorted(results):
        result = str(results[pool_name])
        print("| " + pool_name.ljust(pool_width) + " | " + result.ljust(result_width) + " |")
    print(separator)


def summarize_results(results):
    if not results:
        return Result.Error
    if any(result == Result.Incompatible for result in results.values()):
        return Result.Incompatible
    return Result.Compatible


if __name__ == "__main__":
    type_files = EXAMPLES
    os.system("rm -rf " + ERROR_DIR)
    compat_count = 0
    incompat_count = 0
    error_count = 0
    for file in type_files:
        print("==================================================================================")
        base_name = os.path.basename(file)
        results = run_compat(file)
        table_of_results(results)
        result = summarize_results(results)
        match result:
            case Result.Compatible:
                compat_count += 1
            case Result.Incompatible:
                incompat_count += 1
            case Result.Error:
                error_count += 1
        print("Result for " + base_name + ": " + str(result))
        print("==================================================================================")

    print("==================================================================================")
    print("Summary (OPEN, -debug-choice 4):")
    print("Compatible: " + str(compat_count))
    print("Incompatible: " + str(incompat_count))
    print("Error: " + str(error_count))
    print("==================================================================================")
