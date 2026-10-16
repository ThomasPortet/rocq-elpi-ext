;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "jflart"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("jflart" "")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1")))
   (TeX-run-style-hooks
    "latex2e"
    "jflart10"
    "inputenc"
    "fontenc")
   (TeX-add-symbols
    '("cmd" 1))
   (LaTeX-add-labels
    "fig:bienbelle")
   (LaTeX-add-bibliographies))
 :latex)

