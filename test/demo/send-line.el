(defun send-line ()
      "Send line to other window"
      (interactive)
      (kill-ring-save (line-beginning-position)
                      (line-end-position))
      (other-window 1)
      (goto-char (point-max))
      (yank)
      (comint-send-input)
      (other-window 1)
      (forward-line 1)
      (message "Line executed"))

(global-set-key "\C-c\C-r" 'send-line)

(defun send-undo ()
      "Send undo to other window"
      (interactive)
      (other-window 1)
      (goto-char (point-max))
      (insert "undo")
      (comint-send-input)
      (other-window 1)
      (forward-line -1)
      (message "Undone"))

(global-set-key "\C-c\C-u" 'send-undo)