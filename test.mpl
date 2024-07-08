$define ENABLE_VERIFICATION

with(SolveTools, SemiAlgebraic);
with(BasicLemma, lift):

#printlevel := -1;

test := proc(f, g, basis, x)
local sigma, tau;
    sigma, tau := lift(f, g, basis, x);
    lprint(">> Result:");
    lprint(">> sigma", sigma);
    lprint(">> tau", tau);
$ifdef ENABLE_VERIFICATION
    lprint(expand(sigma*f + tau*g));
    lprint(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), sigma <= 0], [x]));
    lprint(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), tau <= 0], [x]));
$endif
end proc;

# ----------
# Terminates
# ----------
#nat := [x+3, (x-2)*(x+1), (x-1)*(x+2), -(x-3)];
#f := 2/3*(x+2)*(x-2);

#test(f, 1+f, nat, x);
#test(f, 2+f, nat, x);
#test(1+f, f, nat, x);
#test(x + 3, -(x-3), nat, x);
# ----------

# Terminates
#test((x+2)*(x-2), 37/6*(x+2)*(x-2)+1, [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3], x);

# Terminates
#test(x+3, -x+3, [-(x+3)*(x-3)], x);

# Terminates
#f := x+3;
#g := -(x+2)*(x-1)*(x-13);
#test(f, g, [f*g], x);

# Terminates
#basis := [-(x+3)*(x+2)*(x-2)*(x-3)*(x-13)*(x+13)];
#t1 := (x+3)*(x+2);
#t2 := -(x-2)*(x-3)*(x-13)*(x+13);
#t2 := -x^4+5*x^3+163*x^2-845*x+1014;
#test(t1, t2, basis, x);

# Terminates
#f1 := (x+2)*(x-2);
#f2 := 259/1500*(x+2)*(x-2)+1;
#Gfix := [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3, -(x+3)*(x-3)];
#test(f1, f2, Gfix, x);

#t1 := (x+1)*x^2*(x-1);
#t2 := -(x+2)*(x-2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+2);
#t2 := -(x+1)*x^2*(x-1)*(x-2);
#test(t1, t2, basis, x);

#basis := [-(x+2)*(x+1)*x^2*(x-1)*(x-2) + 4*x^2*(x+1)^2];
#t1 := (x+1)*x^3;
#t2 := 8+x-x^2;
#test(t1, t2, basis, x);

#t1 := x+2;
#t2 := -(x+1)*(x-1)*(x-2) + 2*(x+2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x+2;
#t2 := -(x+1)*(x-1)*(x-2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x-1;
#t2 := -(x-2)*(x-4)*(x-7);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := x+3;
#t2 := -(x+2)*(x+1)*(x-1)*(x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+2)*(x+1);
#t2 := -(x+3)*(x-1)*(x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x^2+1);
#t2 := -(x+2)*(x+1)*(x-1)*(x-2);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := (x+2);
#t2 := -(x+1)*(x-1)*(x-2)*(x-3)*(x-4);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x+1)*(x-1);
#t2 := -t1;
#basis := [t1, t2];
#test((x+1), -(x-1), basis, x);
#test(-(x+1), (x-1), basis, x);

#t1 := -(x-1)*(x-4);
#t2 := (x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-4);
#t2 := (x-1);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-1)*(x-5);
#t2 := (x-2)*(x-4);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-5);
#t2 := (x-1);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x-1)*(x-10);
#t2 := (x-2)*(x-3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

#t1 := -(x+4)*(x-4)*(x-2)*(x-3);
#t2 := (x+1)*(x-1)*(x+2)*(x+3);
#basis := [t1*t2];
#test(t1, t2, basis, x);

t1 := (x+3)*(x+2);
t2 := (x+1)*(x-1);
#t2 := (x-2)*(x-3);
basis := [-(x+4)*(x+3)*(x+2)*(x+1)*(x-1)*(x-2)*(x-3)*(x-4)];
test(t1, t2, basis, x);
