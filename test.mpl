with(SolveTools, SemiAlgebraic);
with(BasicLemma, lift):

nat := [x+3, (x-2)*(x+1), (x-1)*(x+2), -(x-3)];
f := 2/3*(x+2)*(x-2);

sigma, tau := lift(f, 1 + f, nat, x);
print(expand(sigma*f + tau*(1+f)));
print(SemiAlgebraic([op(map(poly -> poly >= 0, nat)), sigma <= 0], [x]));
print(SemiAlgebraic([op(map(poly -> poly >= 0, nat)), tau <= 0], [x]));

#sigma, tau := lift(f, 2 + f, nat, x);
#print(expand(sigma*f + tau*(2+f)));
#print(SemiAlgebraic([op(map(poly -> poly >= 0, nat)), sigma <= 0], [x]));
#print(SemiAlgebraic([op(map(poly -> poly >= 0, nat)), tau <= 0], [x]));

#sigma, tau := lift(1 + f, f, nat, x);
#print(expand(sigma*(1+f) + tau*f));
#print(SemiAlgebraic([op(map(poly -> poly >= 0, nat)), sigma <= 0], [x]));
#print(SemiAlgebraic([op(map(poly -> poly >= 0, nat)), tau <= 0], [x]));
