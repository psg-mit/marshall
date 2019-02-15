(defconst
  marshall-pretty-alist
  '(("forall" . ?∀)
    ("exists" . ?∃)
    ("fun" . ?λ)
    ("->" . ?→)
    ("=>" . ?⇒)
    ("/\\" . ?∧)
    ("\\/" . ?∨)
    ("<>" . ?≠)
    ("real" . ?ℝ)
    ("prop" . ?Σ)
    ("True" . ?⊤)
    ("False" . ?⊥)
    ("bool" . ?𝔹)
    ("~" . ?¬))
  "Prettify rules for Marshall.")

(setq marshall-highlights
      (let* (
            ;; define several category of keywords
            (x-keywords '("let" "default" "fun" "cut" "left" "right" "in" "forall" "exists" "int"))
            (x-types '("real" "bool" "prop" "type"))
            (x-constants '("True" "False" "inf" "mkbool" "is_true" "is_false"))
            (x-events '())
            (x-functions '())

            ;; generate regex string for each category of keywords
            (x-keywords-regexp (regexp-opt x-keywords 'words))
            (x-types-regexp (regexp-opt x-types 'words))
            (x-constants-regexp (regexp-opt x-constants 'words))
            (x-events-regexp (regexp-opt x-events 'words))
            (x-functions-regexp (regexp-opt x-functions 'words)))

        `(
          (,x-types-regexp . font-lock-type-face)
          (,x-constants-regexp . font-lock-constant-face)
          (,x-events-regexp . font-lock-builtin-face)
          (,x-functions-regexp . font-lock-function-name-face)
          (,x-keywords-regexp . font-lock-keyword-face)
          ;; note: order above matters, because once colored, that part won't change.
          ;; in general, put longer words first
          )))

(defvar marshall-mode-syntax-table nil "Syntax table for `marshall-mode'.")

(setq marshall-mode-syntax-table
      (let ( (synTable (make-syntax-table)))
        ;; Marshall style comment: “! …”
        (modify-syntax-entry ?! "<" synTable)
        (modify-syntax-entry ?\n ">" synTable)
        (modify-syntax-entry ?_ "w" synTable)
        synTable))

(define-derived-mode marshall-mode
            prog-mode "Marshall"
            "Major mode for Marshall."
            (setq prettify-symbols-alist marshall-pretty-alist)
            (setq font-lock-defaults '(marshall-highlights))
)


(add-hook 'marshall-mode-hook #'prettify-symbols-mode) ;;

(setq auto-mode-alist
(cons '("\\.asd" . marshall-mode) auto-mode-alist))
