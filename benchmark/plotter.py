import argparse
import os
from typing import Optional

import pandas
from matplotlib import pyplot as plt
from enum import Enum
from dataclasses import dataclass

from runner import CASCCategory, SelectionStrategy, Variant


class Mode(Enum):
    TIME = "time"  # plot the total runtime and cumulative problems solved
    COMP = "comp"  # compare first-neg qprover with e and zipper


@dataclass
class Experiment:
    variant: Variant
    duration: int  # in seconds
    category: Optional[CASCCategory]
    basename: Optional[str]

    def to_filename(self):
        if self.category is not None:
            return f"{self.variant.value}_{self.category.value}_{self.duration}"
        else:
            assert (
                self.basename is not None
            ), "No config file given for variant without CASCCategory!"
            return f"{self.basename}_{self.duration}"


def plot(mode: Mode, variant: Variant, duration: int, filename: Optional[str]):
    fig, ax = plt.subplots()
    if mode is Mode.TIME:
        strategies = SelectionStrategy
    else:
        strategies = [SelectionStrategy.SELECTFIRSTNEGLIT]

    for sel_strategy in strategies:
        if variant is Variant.CUSTOM:
            basename = os.path.splitext(os.path.basename(filename))[0]
            experiments = [
                Experiment(
                    variant=variant,
                    duration=duration,
                    category=None,
                    basename=basename,
                )
            ]
        else:
            experiments = [
                Experiment(
                    variant=variant,
                    duration=duration,
                    category=category,
                    basename=None,
                )
                for category in [CASCCategory.FOF, CASCCategory.FNT]
            ]

        for experiment in experiments:
            df = pandas.read_csv(f"{experiment.to_filename()}_{sel_strategy.value}.csv")
            if experiment.category is CASCCategory.FOF:
                fof_problem_size = len(df)
            elif experiment.category is CASCCategory.FNT:
                fnt_problem_size = len(df)
            else:
                problem_size = len(df)
            times = []
            for _, row in df.iterrows():
                if row["expected_result"] == row["result"]:
                    times.append(row["duration"])
            if experiment.variant is Variant.CUSTOM:
                if mode is Mode.COMP:
                    label = f"q_{sel_strategy.value}"
                else:
                    label = f"{sel_strategy.value}"
            else:
                label = f"{experiment.category.value.upper()}: {sel_strategy.value}"
            if sel_strategy is SelectionStrategy.NOSELECTION:
                marker = "o"
            elif sel_strategy is SelectionStrategy.SELECTFIRSTNEGLIT:
                marker = "x"
            elif sel_strategy is SelectionStrategy.SELECTFIRSTMAXIMALNEGLIT:
                marker = "^"
            else:
                assert False
            times.sort()
            ax.plot(
                times,
                [i for i in range(1, len(times) + 1)],
                marker=marker,
                fillstyle="none",
                label=label,
            )

    if mode is Mode.COMP:
        for idx, prefix in enumerate(
            [
                "e_default",
                "e_auto",
                "zipper_no-simpl",
                "zipper_default",
            ]
        ):
            for experiment in experiments:
                df = pandas.read_csv(f"{prefix}_{experiment.to_filename()}.csv")
                if experiment.category is CASCCategory.FOF:
                    fof_problem_size = len(df)
                elif experiment.category is CASCCategory.FNT:
                    fnt_problem_size = len(df)
                else:
                    problem_size = len(df)
                times = []
                for _, row in df.iterrows():
                    if row["expected_result"] == row["result"]:
                        times.append(row["duration"])
                if experiment.variant is Variant.CUSTOM:
                    label = prefix
                else:
                    label = f"{experiment.category.value.upper()}: {prefix}"
                if idx == 0:
                    marker = "v"
                elif idx == 1:
                    marker = "^"
                elif idx == 2:
                    marker = "o"
                elif idx == 3:
                    marker = "s"
                else:
                    assert False
                times.sort()
                ax.plot(
                    times,
                    [i for i in range(1, len(times) + 1)],
                    marker=marker,
                    fillstyle="none",
                    label=label,
                )

    ax.grid(True, linestyle="--")
    ax.set_xlabel("Duration [s]")
    ax.set_ylabel("Solved Problems")
    ax.set_xlim(xmin=0, xmax=duration)
    # ax.set_yscale("log")
    if variant is Variant.CUSTOM:
        ax.legend(loc="lower right")
    else:
        # ax.legend(loc="center")
        ax.legend(loc="upper left", bbox_to_anchor=(1, 1))
    plt.tight_layout()

    first_experiment = experiments[0]
    basename = first_experiment.basename
    mode_name = "cumulative" if mode is Mode.TIME else "comp"
    if basename is not None:
        name = f"../presentation/{mode_name}_{basename}.svg"
        if basename == "pelletier":
            title_var = "Pelletier Problems"
        else:
            title_var = f"TPTP '{basename}' ({problem_size} problems)"
    else:
        name = f"../presentation/{mode_name}_{first_experiment.variant.value}.svg"
        title_var = f"{first_experiment.variant.value.upper()} ({fof_problem_size} FOF, {fnt_problem_size} FNT)"
    ax.set_title(f"{title_var} w/ 1GB mem limit")
    fig.savefig(name, bbox_inches="tight")
    plt.close()


def main():
    parser = argparse.ArgumentParser(description="Plot some measurements")
    parser.add_argument(
        "-d",
        "--duration",
        help="Duration of the measurement",
        required=True,
    )
    parser.add_argument(
        "-f",
        "--file",
        help="File path to the desired run config toml file",
    )
    parser.add_argument(
        "-v",
        "--variant",
        type=Variant,
        choices=list(Variant),
        help="Lowercase!",
        required=True,
    )
    parser.add_argument(
        "-m",
        "--mode",
        type=Mode,
        choices=list(Mode),
        help="Lowercase!",
        required=True,
    )
    args = parser.parse_args()
    variant = Variant(args.variant)
    mode = Mode(args.mode)
    plot(mode, variant, int(args.duration), args.file)


if __name__ == "__main__":
    main()
