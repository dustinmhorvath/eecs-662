:load abe.hs
interp "true"
interp "10"
interp "9+1"
interp "0+7+3"
interp "6+(4+0)"
interp "(0+10)+0"
interp "(2*10)-(30/2)+5"
interp "if 1<=2 then 10 else 0"
interp "if 2<=2 then 10 else 0"
interp "if 3<=2 then 0 else 10"
interp "if (isZero 0) then 10 else 0"
interp "if (isZero 5) then 0 else 10"
interp "if true then 10 else 0"
interp "if false then 0 else 10"
interp "if true then true else false"
interp "if false then true else false"
interp "5*2"
interp "20/2"
interp "21/2"
interp "true && true"
interp "false && true"
interp "true && false"
interp "false && false"
interp "if 1 then 2 else 3"
interp "isZero true"
interp "1/0"