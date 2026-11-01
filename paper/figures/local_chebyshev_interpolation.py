"""Illustrate S2 using LaTeX typography at the manuscript's printed text size."""
from pathlib import Path
import os
os.environ.setdefault("MPLCONFIGDIR", "/private/tmp/local_chebyshev_matplotlib")
os.environ["PATH"] = "/Library/TeX/texbin:" + os.environ.get("PATH", "")
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
import numpy as np
from numpy.polynomial.chebyshev import chebfit, chebval

OUT = Path(__file__).resolve().parent
INK = "#252525"
TAB10 = plt.get_cmap("tab10").colors
BLUE, ORANGE, GREEN, GRAY = (TAB10[i] for i in (0, 1, 2, 7))
# The 3p manuscript has a 468 TeX-point text width. Convert TeX points to
# inches and PostScript points to control the final printed font sizes.
TEXT_WIDTH = 468 / 72.27
FONT_SIZE = 10.5 * 72 / 72.27
TITLE_SIZE = 11 * 72 / 72.27
plt.rcParams.update({
    "font.family": "serif", "font.serif": ["Computer Modern Roman"],
    "font.size": FONT_SIZE, "text.usetex": True,
    "text.latex.preamble": r"\usepackage{amsfonts}",
    "text.color": INK, "axes.labelcolor": INK,
    "xtick.color": INK, "ytick.color": INK, "savefig.facecolor": "white",
})
fig = plt.figure(figsize=(TEXT_WIDTH, 2.35), facecolor="white")
left = fig.add_axes([0.035, 0.32, 0.26, 0.42])
middle = fig.add_axes([0.40, 0.32, 0.235, 0.42])
for center, title in ((.165, "Overlapping intervals"),
                      (.5175, "Local interpolation"), (.85, "Prony series\nmemory kernel")):
    fig.text(center, .95, title, ha="center", va="top", fontsize=TITLE_SIZE,
             linespacing=1.05)

# Supports of the hat partition for logarithmic span 4 and spacing 1.
intervals = [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]
# Two nodes keep the interpolation error visible at manuscript size.
m = 2
nodes = np.sort(np.cos((2 * np.arange(1, m + 1) - 1) * np.pi / (2 * m)))
for row, (lo, hi) in enumerate(intervals):
    height = 5 - row
    color = GREEN if row == 2 else GRAY
    left.plot([lo, hi], [height, height], color=color, lw=2.5, solid_capstyle="butt")
    for endpoint in (lo, hi):
        left.plot([endpoint, endpoint], [height - .15, height + .15], color=color, lw=.8)
left.scatter(2 + nodes, np.full(m, 3), color=GREEN, edgecolor="white", linewidth=.5, s=17, zorder=4)
left.axhline(0, color=INK, lw=.65)
left.set(xlim=(-.12, 4.12), ylim=(-.05, 5.6))
left.set_xticks([0, 4], [r"$\lambda_{\min}$", r"$\lambda_{\max}$"])
left.set_yticks([])
left.tick_params(axis="x", length=0, pad=4)
left.set_xlabel("Relaxation rate $\\lambda$\n(log scale)", labelpad=5)
left.xaxis.set_label_coords(.5, -.38)
for spine in left.spines.values():
    spine.set_visible(False)

# One actual scalar weighted response: e(s)=sin(s), t=2, beta_elas/beta_visc=1,
# and lambda=exp(2+x), with its linear Chebyshev interpolant.
def response(x):
    lam = np.exp(2 + x)
    return (1 + lam) * (lam * np.cos(2) + np.sin(2) - lam * np.exp(-2 * lam)) / (1 + lam**2)
x = np.linspace(-1, 1, 501)
values = response(nodes)
coefficients = chebfit(nodes, values, m - 1)
interpolant = chebval(x, coefficients)
middle.fill_between(x, response(x), interpolant, color=ORANGE, alpha=.16,
                    linewidth=0, zorder=0)
middle.plot(x, response(x), color=BLUE, lw=1.3, label="Weighted response")
middle.plot(x, interpolant, color=ORANGE, lw=1.15, linestyle=(0, (3, 2)), label="Interpolant")
middle.scatter(nodes, values, color=GREEN, edgecolor="white", linewidth=.5, s=17, zorder=4)
ymin, ymax = response(x).min(), response(x).max()
base = ymin - .20 * (ymax - ymin)
for xi, yi in zip(nodes, values):
    middle.plot([xi, xi], [base, yi], color=GRAY, lw=.6, linestyle=(0, (2, 2)), zorder=0)
middle.axhline(base, color=INK, lw=.65)
middle.scatter(nodes, np.full(m, base), color=GREEN, edgecolor="white", linewidth=.5, s=17, zorder=4, clip_on=False)
middle.set(xlim=(-1.08, 1.08), ylim=(base, ymax + .12 * (ymax - ymin)))
middle.set_xticks([])
middle.set_yticks([])
middle.set_xlabel("Relaxation rate $\\lambda$\n(log scale)", labelpad=5)
middle.xaxis.set_label_coords(.5, -.38)
middle.legend(loc="upper right", bbox_to_anchor=(1, 1.30), frameon=False, handlelength=1.0,
              handletextpad=.35, borderaxespad=0, labelspacing=.15)
for spine in middle.spines.values():
    spine.set_visible(False)

arrows = []
for start, end in ((.315, .378), (.650, .696)):
    arrow = FancyArrowPatch((start, .55), (end, .55), transform=fig.transFigure,
                            arrowstyle="-|>", mutation_scale=8, lw=.8, color=INK)
    fig.add_artist(arrow)
    arrows.append(arrow)
fig.text(.3465, .64, "Zoom", ha="center", va="center")
equation = fig.text(.85, .55, r"$\mathbb{K}^{(n)}(t)=\sum_{k=1}^{n}\mathbb{K}_k e^{-\lambda_k t}$", ha="center", va="center")
fig.text(.85, .34, r"$\lambda_k$: fixed relaxation rate", ha="center", va="center")
fig.text(.85, .22, r"$\mathbb{K}_k$: tensor weight", ha="center", va="center")

fig.canvas.draw()
renderer = fig.canvas.get_renderer()
gap = (equation.get_window_extent(renderer).x0 - arrows[1].get_window_extent(renderer).x1) * 72.27 / fig.dpi
print(f"Arrow-to-equation clearance: {gap:.1f} TeX pt; labels: 10.5pt; headings: 11pt")
if gap < 10:
    raise ValueError("The equation needs at least 10pt of clearance from the arrow.")
for extension in ("pdf", "svg", "png"):
    fig.savefig(OUT / f"local_chebyshev_interpolation.{extension}", dpi=250)
plt.close(fig)
