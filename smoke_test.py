import os
import re
import subprocess
from enum import Enum


EXAMPLE_DIR = os.path.join(os.path.dirname(__file__), "session_examples")
FILES = ["test_positive_compat.anvil", "test_negative_compat.anvil"]
ERROR_DIR = os.path.join(os.path.dirname(__file__), "error_logs")
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



# copy the result in error directory by appending error as prefix to the file name
def error_handler(out_log,file_name):
    if not os.path.exists(ERROR_DIR):
        os.makedirs(ERROR_DIR)
    file_base_name = os.path.basename(file_name)
    error_file = os.path.join(ERROR_DIR, "error_" + file_base_name + ".log")
    os.rename(out_log, error_file)


# Find String with "Game Analysis Completed : %b\n  (%b) is the answer"  ;

def result_handler(out_log,file_name):
    # Pool p13 Compatibility: true
    # we will collect all pool names vs there results and at the end display a table of all results
    results = {}
    with open(out_log, 'r') as f:
        for line in f:
            if "Compatibility: true" in line:
                # Extract pool name and result
                regex = r"Pool (\w+) Compatibility: true"
                match = re.search(regex, line)
                if match:
                    pool_name = match.group(1)
                    results[pool_name] = Result.Compatible
            elif "Compatibility: false" in line:
                # Extract pool name and result
                regex = r"Pool (\w+) Compatibility: false"
                match = re.search(regex, line)
                if match:
                    pool_name = match.group(1)
                    results[pool_name] = Result.Incompatible

    error_handler(out_log, file_name)
    return results


def run_compat(file,mode):
    file_base = os.path.basename(file)
    print("Running compatibility check on file: " + file_base)
    compat_temp_log = os.path.join(EXAMPLE_DIR, "compat_temp.txt")
    relative_file = os.path.relpath(file, BASE_DIR)
    # dune exec anvil -- -debug-choice 3 session_examples/test_positive_compat.anvil

    command = ["dune", "exec", "anvil", "--", "-debug-choice", str(mode), relative_file]
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
    if all(result == Result.Incompatible for result in results.values()):
        return Result.Incompatible
    elif all(result == Result.Compatible for result in results.values()):
        return Result.Compatible
    else:
        return Result.Error

if __name__ == "__main__":
    mode = 3
    type_files = EXAMPLES
    if os.sys.argv[1:]:
        mode = int(os.sys.argv[1])
    else:
        print("No mode specified, defaulting to mode 3 (compatibility check).")
    os.system("rm -rf " + ERROR_DIR)
    compat_count = 0
    incompat_count = 0
    error_count = 0
    for file in type_files:
        print("==================================================================================")
        base_name = os.path.basename(file)
        results = run_compat(file,mode )
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
    print("Summary:")
    print("Compatible: " + str(compat_count))
    print("Incompatible: " + str(incompat_count))
    print("Error: " + str(error_count))
    print("==================================================================================")

