;;; heft.el --- Major mode for a language definition language. -*- lexical-binding: t -*-

;; hack
(defun heft-unindent ()
  "remove 2 spaces from beginning of of line"
  (interactive)
  (save-excursion
    (save-match-data
      (beginning-of-line)
      ;; get rid of tabs at beginning of line
      (when (looking-at "^\\s-+")
        (untabify (match-beginning 0) (match-end 0)))
      (when (looking-at "^  ")
        (replace-match "")))))

(setq heft-font-lock-keywords
      (let* (
             (symbols-regex '"\\\\\\|\|\\|!\\|{\\|}\\|/\\|(\\|)\\|->\\|<\\|>\\|*\\|,\\|:")
             (x-keywords '("data" "effect" "val" "end" "match" "handle"))

             (x-keywords-regexp (regexp-opt x-keywords 'symbols))
             )
        `(
          (,x-keywords-regexp . font-lock-keyword-face)
          (,symbols-regex . font-lock-constant-face)
         )))

(defconst heft-mode-syntax-table
  (let ((table (make-syntax-table)))
       (modify-syntax-entry ?\{  "(}1nb" table)
       (modify-syntax-entry ?\}  "){4nb" table)
       (modify-syntax-entry ?-  "_ 123" table)
       (modify-syntax-entry ?\n ">" table)
    table))

(define-derived-mode heft-mode prog-mode "heft mode"
  "Major mode for editing language definition files."
  
  :syntax-table heft-mode-syntax-table

  (progn
    (setq-local font-lock-defaults '(heft-font-lock-keywords))
    (setq-local comment-start "--")
    (setq-local comment-end "")
    (setq major-mode 'heft-mode)
    (setq mode-name "heft")
    (use-local-map heft-mode-map)
    (run-hooks 'heft-mode-hook)
    (local-set-key (kbd "<backtab>") 'heft-unindent)
    (setq-local tab-width 2)
    (setq-local heft-output-buffer nil)))

(provide 'heft-mode)
