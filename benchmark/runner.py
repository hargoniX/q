import argparse
from subprocess import run, PIPE
import os
import tomllib
import resource
from dataclasses import dataclass
from enum import Enum
from typing import Optional, List
from multiprocessing import Pool
from datetime import datetime

EXCLUDE_LIST = []
NUM_THREADS = 16
# This is a limit per thread!
MEM_LIMIT = 10**9


class Variant(Enum):
    PELLETIER = "pelletier"
    CASC24 = "casc24"
    CASC29 = "casc29"


class CASCCategory(Enum):
    FOF = "fof"  # provable
    FNT = "fnt"  # counterexample


class Result(Enum):
    SAT = "StatementFalse"
    UNSAT = "ProofFound"
    TIMEOUT = "Unknown(Timeout)"
    UNKNOWN = "Unknown()"


class SelectionStrategy(Enum):
    NOSELECTION = "no-sel"
    SELECTFIRSTNEGLIT = "first-neg"
    SELECTFIRSTMAXIMALNEGLIT = "zipper-sel"


@dataclass
class Problem:
    filename: str
    expected_result: Result
    result: Optional[Result]
    execution_time: Optional[float]


def build():
    print("Build release target:")
    run(["cargo", "build", "--release"], stdout=PIPE, stderr=PIPE)


def set_limits(duration: int):
    # (soft_limit, hard_limit)
    # cpu time in seconds
    resource.setrlimit(resource.RLIMIT_CPU, (duration, duration))
    # heap size in bytes
    resource.setrlimit(resource.RLIMIT_DATA, (MEM_LIMIT, MEM_LIMIT))


def get_problems(filename: str) -> List[Problem]:
    with open(filename, "rb") as f:
        config = tomllib.load(f)
    problems = []
    for problem in config["problems"]:
        problem = config["problems"][problem]
        filename = problem["filename"]
        match problem["result"]:
            case "SAT":
                exp_result = Result.SAT
            case "UNSAT":
                exp_result = Result.UNSAT
            case "TIMEOUT":
                exp_result = Result.TIMEOUT
            case _:
                exp_result = Result.UNKNOWN
        problems.append(
            Problem(
                filename=filename,
                expected_result=exp_result,
                result=None,
                execution_time=None,
            )
        )

    return problems


def get_problems_casc(variant: Variant, category: CASCCategory) -> List[Problem]:
    problems = []
    base = f"problems/{variant.value}"
    if category is CASCCategory.FOF:
        expected_result = Result.UNSAT
        problem_sets = ["FEQ", "FNE"]
    elif category is CASCCategory.FNT:
        expected_result = Result.SAT
        problem_sets = ["FNN", "FNQ"]
    else:
        assert False, f"No controlflow for given variant '{variant.value}'"
    for problem_set in problem_sets:
        path = f"{base}/{problem_set}"
        if variant is Variant.CASC29:
            path += f"/{problem_set}ProblemFiles"
        files = [f for f in os.listdir(path) if os.path.isfile(os.path.join(path, f))]
        for problem in files:
            if problem not in EXCLUDE_LIST:
                problems.append(
                    Problem(
                        filename=f"{path}/{problem}",
                        expected_result=expected_result,
                        result=None,
                        execution_time=None,
                    )
                )

    return problems


def test(
    problem: Problem, duration: int, selection_strategy: SelectionStrategy
) -> Problem:
    env = os.environ.copy()
    env["RUST_LOG"] = "WARN"
    # Using cargo with multiple threads is a bottleneck
    cmd = [
        "../zipperposition.exe",
        problem.filename,
        "--timeout",
        str(duration),
        "--mem-limit",
        str(MEM_LIMIT // 1_000_000),
        "--dont-simplify",
        "--avatar",
        "off",
    ]
    start = datetime.now()
    output = run(
        cmd,
        env=env,
        stdout=PIPE,
        stderr=PIPE,
        universal_newlines=True,
        preexec_fn=set_limits(duration + 5 if duration else 1),
    ).stdout
    end = datetime.now()
    if f"Satisfiable" in output:
        result = Result.SAT
    elif f"Refutation" in output:
        result = Result.UNSAT
    elif f"ResourceOut" in output:
        result = Result.TIMEOUT
    else:
        print(f"Result is Unknown: stdout'{output}'")
        result = Result.UNKNOWN
    return Problem(
        filename=problem.filename,
        expected_result=problem.expected_result,
        result=result,
        execution_time=(end - start).total_seconds(),
    )


@dataclass
class ResultLists:
    matching_problems: List[Problem]
    non_matching_problems: List[Problem]
    timeout_problems: List[Problem]
    unknown_problems: List[Problem]


def go(
    problems: List[Problem],
    duration: int,
    results: ResultLists,
    selection_strategy: SelectionStrategy,
) -> ResultLists:
    for problem in problems:
        print(f"Running {problem.filename}")
        problem = test(problem, duration, selection_strategy)
        if problem.result is problem.expected_result:
            results.matching_problems.append(problem)
            print(
                f"{problem.filename} PASS: expected {problem.expected_result} got {problem.result}"
            )
        else:
            print(
                f"{problem.filename} FAIL: expected {problem.expected_result} got {problem.result}"
            )
            if problem.result is Result.TIMEOUT:
                results.timeout_problems.append(problem)
            elif problem.result is Result.UNKNOWN:
                results.unknown_problems.append(problem)
            else:
                results.non_matching_problems.append(problem)
                print(f"Non-matching!")
    return results


def main():
    parser = argparse.ArgumentParser(
        description=f"Run some measurements defined by a config file"
    )
    parser.add_argument(
        "-f",
        "--file",
        help="File path to the desired run config toml file",
    )
    parser.add_argument(
        "-d",
        "--duration",
        type=int,
        help="Timeout duration for a single prover run",
    )
    parser.add_argument(
        "-m",
        "--mode",
        type=Variant,
        choices=list(Variant),
        help="Lowercase!",
    )
    parser.add_argument(
        "-c",
        "--category",
        type=CASCCategory,
        choices=list(CASCCategory),
        help="Lowercase!",
    )
    parser.add_argument(
        "-s",
        "--selection-strategy",
        type=SelectionStrategy,
        choices=list(SelectionStrategy),
        help="Lowercase!",
    )
    args = parser.parse_args()
    root_dir = run(
        ["git", "rev-parse", "--show-toplevel"],
        stdout=PIPE,
        stderr=PIPE,
        universal_newlines=True,
    ).stdout.rstrip()
    os.chdir(root_dir)
    # build()
    variant = args.mode
    if variant is Variant.PELLETIER:
        assert args.file is not None, "No config file given for pelletier variant!"
        problems = get_problems(args.file)
        print(f"Start Testsuite 'pelletier' with '{args.file}'")
    elif variant in [Variant.CASC24, Variant.CASC29]:
        print(f"Start Testsuite '{variant.value}' for category '{args.category.value}'")
        problems = get_problems_casc(variant, args.category)
    else:
        assert False, f"No controlflow for given variant '{variant.value}'"
    print(80 * "-")

    pool = Pool()
    thread_list = []
    for i in range(NUM_THREADS):
        thread_list.append(
            pool.apply_async(
                go,
                [
                    problems[i::NUM_THREADS],
                    args.duration,
                    ResultLists([], [], [], []),
                    args.selection_strategy,
                ],
            )
        )

    matching_problems: List[Problem] = []
    non_matching_problems: List[Problem] = []
    timeout_problems: List[Problem] = []
    unknown_problems: List[Problem] = []
    for thread in thread_list:
        results: ResultLists = thread.get(timeout=args.duration * 1500)
        matching_problems.extend(results.matching_problems)
        non_matching_problems.extend(results.non_matching_problems)
        timeout_problems.extend(results.timeout_problems)
        unknown_problems.extend(results.unknown_problems)

    if args.category is not None:
        out_file = f"benchmark/{variant.value}_{args.category.value}_{args.duration}_{args.selection_strategy.value}"
    else:
        filename_wo_ext = os.path.splitext(os.path.basename(args.file))[0]
        out_file = f"benchmark/{filename_wo_ext}_{args.duration}_{args.selection_strategy.value}"
    summary_file = f"{out_file}.summary"
    print(80 * "-")
    summary_str = f"""There are:
- {len(matching_problems)} matching results
- {len(non_matching_problems)} non-matching results
- {len(timeout_problems)} timeout results
- {len(unknown_problems)} 'unknown' results
"""
    print(summary_str)
    with open(summary_file, "w") as f:
        f.write(summary_str)
    print(80 * "-")
    csv_file = f"{out_file}.csv"
    print(f"Writing summary output files: '{csv_file}' and '{summary_file}'")
    with open(csv_file, "w") as f:
        f.write("problem,expected_result,result,duration\n")
        result_set = non_matching_problems
        result_set.extend(matching_problems)
        result_set.extend(timeout_problems)
        result_set.extend(unknown_problems)
        result_set.sort(key=lambda x: x.filename)
        for problem in result_set:
            basename = os.path.basename(problem.filename)
            execution_time = (
                f"{problem.execution_time:.2f}"
                if args.duration == 1
                else f"{problem.execution_time:.1f}"
            )
            f.write(
                f"{basename},{problem.expected_result.value},{problem.result.value},{execution_time}\n"
            )


if __name__ == "__main__":
    main()
