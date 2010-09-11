;; ****************************************************************
;; Command line shortcuts
;; ****************************************************************

;; Window with code
(setq code-win (selected-window))
;; Window with Pig running
(setq pig-win 'nil)

(defun may-open-pig () ""
  (if (not pig-win)
      (open-pig)))

(defun open-pig ()
      "Open Pig"
      (setq pig-win (split-window code-win 'nil 'nil))
      (select-window pig-win)
      (setq shell-file-name "Pig")
      (shell)
      (select-window code-win)
      (message "Pig opened"))

(defun send-line ()
      "Send line to Pig"
      (may-open-pig)
      (interactive)
      (kill-ring-save (line-beginning-position)
                      (line-end-position))
      (select-window pig-win)
      (goto-char (point-max))
      (yank)
      (comint-send-input)
      (select-window code-win)
      (forward-line 1)
      (message "Line executed"))

(defun send-undo ()
      "Send undo to Pig"
      (may-open-pig)
      (interactive)
      (select-window pig-win)
      (goto-char (point-max))
      (insert "undo")
      (comint-send-input)
      (select-window code-win)
      (forward-line -1)
      (message "Undone"))

(defun send-show-state ()
      "Send 'show state' to Pig"
      (may-open-pig)
      (interactive)
      (select-window pig-win)
      (goto-char (point-max))
      (insert "show state")
      (comint-send-input)
      (select-window code-win)
      (message "State shown"))


;; ****************************************************************
;; Syntax highlighting
;; ****************************************************************


(defvar pig-commands
  '("data" "idata" "let" "refine" "load" "module"))
(defvar pig-commands-regexp (regexp-opt pig-commands 'words))

(defvar pig-tactics
  '("apply" "bottom" "compile" "define" "done" 
    "down" "elab" "eliminate"
    "elm" "execute" "first" "give"
    "haskell" "help" "in" "infer" 
    "jump" "lambda" "last" "make" 
    "match" "next" "out" "parse" "pi"
    "previous" "program" "propsimplify"
    "quit" "relabel" "root" "save" "scheme"
    "show" "simplify" "solve" "top" "undo" 
    "ungawa" "up" "validate" "whatis"))
(defvar pig-tactics-regexp (regexp-opt pig-tactics 'words))


(defvar pig-mode-font-lock-keywords
  `((,pig-commands-regexp . font-lock-keyword-face)
    ("\\(:=\\|<=\\|= \\)" . font-lock-keyword-face)
    ("'[[:alnum:]]*" . font-lock-type-face)
    (,pig-tactics-regexp . font-lock-builtin-face)
    (";\n" . font-lock-builtin-face)
    ))


;; ****************************************************************
;; Support for comments
;; ****************************************************************

(defun pig-comment-dwim (arg)
"Comment or uncomment current line or region in a smart way.
For detail, see `comment-dwim'."
   (interactive "*P")
   (require 'newcomment)
   (let ((deactivate-mark nil) 
	 (comment-start "--") (comment-end "")
	 (comment-start "{-") (comment-end "-}"))
     (comment-dwim arg)))


;; ****************************************************************
;; Major mode definition
;; ****************************************************************


(define-derived-mode pig-mode fundamental-mode "Cochon"
  "Major mode to chat with Cochon."
 
  ;; Set font-lock 
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(pig-mode-font-lock-keywords))

  ;; Set shortcuts
  (define-key pig-mode-map [remap comment-dwim] 'pig-comment-dwim)
  (define-key pig-mode-map "\C-c\C-r" 'send-line)
  (define-key pig-mode-map "\C-c\C-u" 'send-undo)
  (define-key pig-mode-map "\C-c\C-s" 'send-show-state)

  ;; Syntax table for comments
  (modify-syntax-entry ?- ". 12b" pig-mode-syntax-table)
  (modify-syntax-entry ?\n "> b" pig-mode-syntax-table)
  (modify-syntax-entry ?{ ". 1" pig-mode-syntax-table)
  (modify-syntax-entry ?} ". 4" pig-mode-syntax-table)
  (modify-syntax-entry ?- ". 23" pig-mode-syntax-table)

  ;; Set font-lock
  (font-lock-mode))


(add-to-list 'auto-mode-alist '("\\.pig\\'" . pig-mode))
(provide 'pig-mode)