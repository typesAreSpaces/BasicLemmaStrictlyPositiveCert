with(SolveTools, SemiAlgebraic);
with(BasicLemma, lift):

#printlevel := -1;

test := proc(f, g, basis, x)
local sigma, tau;
    sigma, tau := lift(f, g, basis, x);
    lprint(expand(sigma*f + tau*g));
    lprint(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), sigma <= 0], [x]));
    lprint(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), tau <= 0], [x]));
end proc;

#nat := [x+3, (x-2)*(x+1), (x-1)*(x+2), -(x-3)];
#f := 2/3*(x+2)*(x-2);

#test(f, 1+f, nat, x);
#test(f, 2+f, nat, x);
#test(1+f, f, nat, x);
#test(x + 3, -(x-3), nat, x);

#test(
#(x+2)*(x-2), 
#37/6*(x+2)*(x-2)+1,
#[x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3], 
#x);

#test(
#x+3, -x+3, [-(x+3)*(x-3)], x
#);

#f := x+3;
#g := -(x+2)*(x-1)*(x-13);
#s, t := test(f, g, [f*g], x);

#lprint(expand(s*f + t*g));
#lprint(">> s", s);
#lprint(">> t", t);

#basis := [-(x+3)*(x+2)*(x-2)*(x-3)*(x-13)*(x+13)];
#t1 := (x+3)*(x+2);
#t2 := -x^4+5*x^3+163*x^2-845*x+1014;
#t2 := -(x-2)*(x-3)*(x-13)*(x+13);
#lprint(">> args", t1, t2, basis, x);
#s, t := test(t1, t2, basis, x);

#lprint(expand(s*t1 + t*t2));
#lprint(">> s", s);
#lprint(">> t", t);


f1 := (x+2)*(x-2);
f2 := 259/1500*(x+2)*(x-2)+1;
Gfix := [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3, -(x+3)*(x-3)];

test(f1, f2, Gfix, x);
