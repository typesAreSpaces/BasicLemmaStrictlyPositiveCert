with(SolveTools, SemiAlgebraic);
with(BasicLemma, lift):

#printlevel := -1;

test := proc(f, g, basis, x)
local sigma, tau;
    sigma, tau := lift(f, g, basis, x);
    #print(expand(sigma*f + tau*g));
    #print(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), sigma <= 0], [x]));
    #print(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), tau <= 0], [x]));
end proc;

#nat := [x+3, (x-2)*(x+1), (x-1)*(x+2), -(x-3)];
#f := 2/3*(x+2)*(x-2);

#test(f, 1+f, nat, x);
#test(f, 2+f, nat, x);
#test(1+f, f, nat, x);
#test(x + 3, -(x-3), nat, x);

test(
(x+2)*(x-2), 
37/6*(x+2)*(x-2)+1,
[x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3], 
x);
