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


def plot_cumulative(variant: Variant, duration: int, filename: Optional[str]):
    fig, ax = plt.subplots()
    for sel_strategy in SelectionStrategy:
        if variant is Variant.PELLETIER:
            basename = os.path.splitext(os.path.basename(filename))[0]
            experiments = [
                Experiment(
                    variant=variant, duration=duration, category=None, basename=basename
                )
            ]
        else:
            experiments = [
                Experiment(
                    variant=variant, duration=duration, category=category, basename=None
                )
                for category in [CASCCategory.FOF, CASCCategory.FNT]
            ]

        for experiment in experiments:
            df = pandas.read_csv(f"{experiment.to_filename()}_{sel_strategy.value}.csv")
            times = []
            for _, row in df.iterrows():
                if row["expected_result"] == row["result"]:
                    times.append(row["duration"])
            if experiment.variant is Variant.PELLETIER:
                label = f"{sel_strategy.value}"
            else:
                label = f"{experiment.category.value}: {sel_strategy.value}"
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

    ax.grid(True, linestyle="--")
    ax.set_xlabel("Duration [s]")
    ax.set_ylabel("Solved Problems")
    ax.set_xlim(xmin=0, xmax=duration)
    # ax.set_yscale("log")
    ax.legend(loc="center right")
    plt.tight_layout()

    first_experiment = experiments[0]
    basename = first_experiment.basename
    if basename is not None:
        name = f"cumulative_{basename}.png"
        if basename == "pelletier":
            title_var = basename
        else:
            title_var = f"TPTP Full: {basename}"
    else:
        name = f"cumulative_{first_experiment.variant.value}.png"
        title_var = first_experiment.variant.value
    ax.set_title(f"Cumulative problems solved at {title_var}")
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
    if args.mode is Mode.TIME:
        plot_cumulative(variant, int(args.duration), args.file)


if __name__ == "__main__":
    main()
