import argparse
from subprocess import run, PIPE
import os
import tomllib
from dataclasses import dataclass
from enum import Enum
from typing import Optional, List
from multiprocessing import Pool

NUM_THREADS = 16


class Result(Enum):
    SAT = "StatementFalse"
    UNSAT = "ProofFound"
    TIMEOUT = "Unknown(Timeout)"
    UNKNOWN = "Unknown()"


@dataclass
class Problem:
    filename: str
    expected_result: Result
    result: Optional[Result]


def build():
    print("Build release target:")
    run(["cargo", "build", "--release"], stdout=PIPE, stderr=PIPE)


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
            Problem(filename=filename, expected_result=exp_result, result=None)
        )

    return problems


def test(problem: Problem, duration: Optional[int]) -> Problem:
    env = os.environ.copy()
    env["RUST_LOG"] = "WARN"
    cmd = ["cargo", "run", "--release", "--", problem.filename]
    if duration is not None:
        cmd.append(str(duration))
    output = run(
        cmd,
        env=env,
        stdout=PIPE,
        stderr=PIPE,
        universal_newlines=True,
    ).stderr
    if f"Result superposition: 'StatementFalse'" in output:
        result = Result.SAT
    elif f"Result superposition: 'ProofFound'" in output:
        result = Result.UNSAT
    elif f"Result superposition: 'Unknown(Timeout)'" in output:
        result = Result.TIMEOUT
    else:
        print(f"Result is Unknown:\n{output}")
        result = Result.UNKNOWN
    return Problem(
        filename=problem.filename,
        expected_result=problem.expected_result,
        result=result,
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
) -> ResultLists:
    for problem in problems:
        print(f"Running {problem.filename}")
        problem = test(problem, duration)
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
        required=True,
    )
    parser.add_argument(
        "-d",
        "--duration",
        type=int,
        help="Timeout duration for a single prover run",
    )
    args = parser.parse_args()
    root_dir = run(
        ["git", "rev-parse", "--show-toplevel"],
        stdout=PIPE,
        stderr=PIPE,
        universal_newlines=True,
    ).stdout.rstrip()
    os.chdir(root_dir)
    build()
    problems = get_problems(args.file)
    print(f"Start Testsuite '{args.file}'")
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
                ],
            )
        )

    matching_problems = []
    non_matching_problems = []
    timeout_problems = []
    unknown_problems = []
    for thread in thread_list:
        results: ResultLists = thread.get(timeout=args.duration * 1500)
        matching_problems.extend(results.matching_problems)
        non_matching_problems.extend(results.non_matching_problems)
        timeout_problems.extend(results.timeout_problems)
        unknown_problems.extend(results.unknown_problems)

    print(80 * "-")
    print("There are:")
    print(f"- {len(matching_problems)} matching results")
    print(f"- {len(non_matching_problems)} non-matching results")
    print(f"- {len(timeout_problems)} timeout results")
    print(f"- {len(unknown_problems)} 'unknown' results")


if __name__ == "__main__":
    main()
