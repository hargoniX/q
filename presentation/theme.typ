// This theme is inspired by https://github.com/matze/mtheme
// The origin code was written by https://github.com/Enivex
#import "@preview/touying:0.6.1": *
#import "@preview/ctheorems:1.1.3": *

#let g_prim = rgb("#00883A") // dark-green LMU
#let g_fg = rgb("#232323") // dark
#let g_bg = rgb("#ffffff") // white

#let th_pres = thmbox("theorem", "Theorem", base: none,
  fill: rgb("#eeffee"), inset: 15pt, breakable: true
)

#let slide(
  title: auto,
  align: auto,
  config: (:),
  repeat: auto,
  setting: body => body,
  composer: auto,
  ..bodies,
) = touying-slide-wrapper(self => {
  if align != auto {
    self.store.align = align
  }
  let header(self) = {
    set std.align(top)
    show: components.cell.with(fill: self.colors.secondary, inset: 1em)
    set std.align(horizon)
    set text(fill: self.colors.neutral-lightest, weight: "medium", size: 28pt)
    components.left-and-right(
      {
        if title != auto {
          utils.fit-to-width(grow: false, 100%, title)
        } else {
          utils.call-or-display(self, self.store.header)
        }
      },
      utils.call-or-display(self, self.store.header-right),
    )
  }
  let footer(self) = {
    set std.align(bottom)
    set text(size: 16pt)
    pad(
      .5em,
      components.left-and-right(
        text(fill: self.colors.neutral-darkest.lighten(40%), utils.call-or-display(self, self.store.footer)),
        text(fill: self.colors.neutral-darkest, utils.call-or-display(self, self.store.footer-right)),
      ),
    )
    if self.store.footer-progress {
      place(bottom, components.progress-bar(height: 3pt, self.colors.primary, self.colors.primary-light))
    }
  }
  let self = utils.merge-dicts(
    self,
    config-page(
      fill: self.colors.neutral-lightest,
      header: header,
      footer: footer,
    ),
  )
  let new-setting = body => {
    show: std.align.with(self.store.align)
    set text(fill: self.colors.neutral-darkest)
    show: setting
    body
  }
  touying-slide(self: self, config: config, repeat: repeat, setting: new-setting, composer: composer, ..bodies)
})


#let title-slide(
  config: (:),
  extra: none,
  ..args,
) = touying-slide-wrapper(self => {
  self = utils.merge-dicts(
    self,
    config,
    config-common(freeze-slide-counter: true),
    config-page(fill: self.colors.neutral-lightest),
  )
  let info = self.info + args.named()
  let body = {
    set text(fill: self.colors.neutral-darkest)
    set std.align(horizon)
    block(
      width: 100%,
      inset: 2em,
      {
        components.left-and-right(
          {
            text(size: 1.3em, text(weight: "medium", info.title))
            if info.subtitle != none {
              linebreak()
              text(size: 0.9em, info.subtitle)
            }
          },
          text(2em, utils.call-or-display(self, info.logo)),
        )
        line(length: 100%, stroke: .05em + self.colors.primary)
        set text(size: .8em)
        if info.author != none {
          block(spacing: 1em, info.author)
        }
        if info.date != none {
          block(spacing: 1em, utils.display-info-date(self))
        }
        set text(size: .8em)
        if info.institution != none {
          block(spacing: 1em, info.institution)
        }
        if extra != none {
          block(spacing: 1em, extra)
        }
      },
    )
  }
  touying-slide(self: self, body)
})


#let new-section-slide(config: (:), level: 1, numbered: true, body) = touying-slide-wrapper(self => {
  let slide-body = {
    set std.align(horizon)
    show: pad.with(20%)
    set text(size: 1.5em)
    stack(
      dir: ttb,
      spacing: 1em,
      text(self.colors.neutral-darkest, utils.display-current-heading(level: level, numbered: numbered)),
      block(
        height: 2pt,
        width: 100%,
        spacing: 0pt,
        components.progress-bar(height: 2pt, self.colors.primary, self.colors.primary-light),
      ),
    )
    text(self.colors.neutral-dark, body)
  }
  self = utils.merge-dicts(
    self,
    config-page(fill: self.colors.neutral-lightest),
  )
  touying-slide(self: self, config: config, slide-body)
})


#let focus-slide(config: (:), align: horizon + center, body) = touying-slide-wrapper(self => {
  self = utils.merge-dicts(
    self,
    config-common(freeze-slide-counter: true),
    config-page(fill: self.colors.neutral-dark, margin: 2em),
  )
  set text(fill: self.colors.neutral-lightest, size: 1.5em)
  touying-slide(self: self, config: config, std.align(align, body))
})


#let lmu-theme(
  aspect-ratio: "16-9",
  align: horizon,
  header: self => utils.display-current-heading(
    setting: utils.fit-to-width.with(grow: false, 100%),
    depth: self.slide-level,
  ),
  header-right: self => self.info.logo,
  footer: none,
  footer-right: self => context{
    let curr = utils.slide-counter.display()
    let last = utils.last-slide-counter.display()
    if curr > last []
    else [#curr / #utils.last-slide-number]
  },
  footer-progress: true,
  ..args,
  body,
) = {
  set text(size: 20pt)
  //set text(font: "Fira Sans", weight: "light", size: 20pt)
  //show math.equation: set text(font: "Fira Math")
  set strong(delta: 100)
  set par(justify: true)

  show: touying-slides.with(
    config-page(
      paper: "presentation-" + aspect-ratio,
      header-ascent: 10%,
      footer-descent: 30%,
      margin: (top: 3em, bottom: 1.5em, x: 2em),
    ),
    config-common(
      slide-fn: slide,
      new-section-slide-fn: none,
    ),
    config-methods(
      alert: utils.alert-with-primary-color,
    ),
    // config-colors(
    //   primary: rgb("#eb811b"),
    //   primary-light: rgb("#d6c6b7"),
    //   secondary: rgb("#23373b"),
    //   neutral-lightest: rgb("#fafafa"),
    //   neutral-dark: rgb("#23373b"),
    //   neutral-darkest: rgb("#23373b"),
    // )
    config-colors(
      primary: rgb("#eb811b"),
      primary-light: rgb("#d6c6b7"),
      secondary: g_prim,
      neutral-lightest: rgb("#fafafa"),
      neutral-dark: rgb("#23373b"),
      neutral-darkest: rgb("#23373b"),
    ),
    // save the variables for later use
    config-store(
      align: align,
      header: header,
      header-right: header-right,
      footer: footer,
      footer-right: footer-right,
      footer-progress: footer-progress,
    ),
    ..args,
  )

  body
}
