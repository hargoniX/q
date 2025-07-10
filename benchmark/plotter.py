import argparse
from typing import Optional

import pandas
from matplotlib import pyplot as plt
from enum import Enum
from dataclasses import dataclass

from runner import CASCCategory, Variant


class Mode(Enum):
    TIME = "time"  # plot the total runtime and cumulative problems solved


@dataclass
class Experiment:
    variant: Variant
    duration: int  # in seconds
    category: Optional[CASCCategory]

    def to_filename(self):
        if self.category is not None:
            return f"{self.variant.value}_{self.category.value}_{self.duration}"
        else:
            return f"{self.variant.value}_{self.duration}"


def plot_cumulative(variant: Variant, duration: int):
    fig, ax = plt.subplots()
    if variant is Variant.PELLETIER:
        experiments = [Experiment(variant=variant, duration=duration, category=None)]
    else:
        experiments = [
            Experiment(variant=variant, duration=duration, category=category)
            for category in [CASCCategory.FOF, CASCCategory.FNT]
        ]

    for experiment in experiments:
        df = pandas.read_csv(f"{experiment.to_filename()}.csv")
        times = []
        for _, row in df.iterrows():
            if row["expected_result"] == row["result"]:
                times.append(row["duration"])
        if experiment.variant is Variant.PELLETIER:
            label = "pelletier"
        else:
            label = f"{experiment.category}"
        times.sort()
        ax.plot(
            times,
            [i for i in range(1, len(times) + 1)],
            marker="o",
            fillstyle="none",
            label=label,
        )

    ax.grid(True, linestyle="--")
    ax.set_xlabel("Duration [s]")
    ax.set_ylabel("Solved Problems")
    ax.set_xlim(xmin=0, xmax=duration)
    # ax.set_xscale("log")
    ax.legend(loc="lower right")
    variant = experiments[0].variant
    ax.set_title(f"Cumulative problems solved at {variant.value}")

    plt.tight_layout()
    name = f"cumulative_{variant.value}.svg"
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
        plot_cumulative(variant, int(args.duration))


if __name__ == "__main__":
    main()
