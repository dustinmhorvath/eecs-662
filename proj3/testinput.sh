:load proj3Utils.hs
interpCFBAE "lambda x in x + 1"
interpCFBAE "bind y = 10 in bind x = (lambda x in y + x) in bind y = 1 in (app x 0)"
interpCFBAE "5 * 2"
interpCFBAE "50 / 5"
interpCFBAE "8 + 2"
interpCFBAE "15 - 5"
interpCFBAE "if0 0 then 10 else 0"
interpCFBAE "if0 1 then 0 else 10"
interpCFBAE "2 + 2 + 2 + 2 + 2"
interpCFBAE "2 + (app (lambda x in x + 5) 3)"
interpCFBAE "bind x = 3 in (x + 7)"
:quit
