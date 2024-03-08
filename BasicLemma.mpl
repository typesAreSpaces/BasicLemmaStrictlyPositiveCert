$define ENABLE_DEBUGGING false
$define ENABLE_VERIFICATION false
$define LOG_TIME
$define BUMP_FINDN 1/10

$define DEBUG_EXIT lprint(">> Debugging, getting out"); return 0
$define DEBUG(F, L, y, x) if (y) then lprint(">> Debugging file ", F, " at line ", L); x; end if

$define START_LOG_TIME(X, S) stack_level:=stack_level+1;fd := Open("log_time.txt", append);local _log_time_S := time();WriteString(fd, cat("Start: ", X, " ", convert(stack_level, string), "\n"));Close(fd);
$define END_LOG_TIME(X, S) fd := Open("log_time.txt", append);WriteString(fd, cat("End: ", X, " ", convert(stack_level, string), "\nTime: ", convert(time() - _log_time_S, string), "\n"));Close(fd);stack_level:=stack_level-1;
$define INIT_START_LOG_TIME(X, S) local fd;START_LOG_TIME(X, S)

with(Algebraic, ExtendedEuclideanAlgorithm);
with(SolveTools, SemiAlgebraic);
with(FileTools, Text);
with(Text, Open, Close, WriteString);

BasicLemma := module() option package;

local stack_level := -1;

local bound_info;
local minPolyOverBasis;

local findN;
local findEps;
local findK;

export lift;

    bound_info := proc(x, bound, eps)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("bound_info",0)
$endif
    local i1, i2, j1, j2;
        # This is a bounded bounduality
        if(nops(bound) = 2) then
            i1 := simplify(op(bound[1])[1]);
            i2 := simplify(op(bound[1])[2]);
            j1 := simplify(op(bound[2])[1]);
            j2 := simplify(op(bound[2])[2]);
            if evalb(i1 = x) then
                if evalb(j1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i2, j2)+eps, max(i2, j2)-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i2, j1)+eps, max(i2, j1)-eps];
                end if;
            else
                if evalb(j1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i1, j2)+eps, max(i1, j2)-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i1, j1)+eps, max(i1, j1)-eps];
                end if;
            end if;
            # This is an equality or unbounded bounduality
        else
            i1 := simplify(op(bound[1])[1]);
            j1 := simplify(op(bound[1])[2]);
            if type(bound[1], `=`) then
                if evalb(i1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [j1, j1];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [i1, i1];
                end if;
            end if;
            if type(bound[1], `<=`) then
                if evalb(i1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [-infinity, j1-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [i1+eps, infinity];
                end if;
            end if;
        end if;
    end proc;

    minPolyOverBasis := proc(f, basis, x);
$ifdef LOG_TIME
        INIT_START_LOG_TIME("minPolyOverBasis",0)
$endif
    local lowerbound, upperbound, interval, output;
        output := min(
            map(proc(bound)
                    interval := bound_info(x, bound, 0);
                    #lowerbound := convert(evalf(interval[1]), rational);
                    #upperbound := convert(evalf(interval[2]), rational);
                    lowerbound := interval[1];
                    upperbound := interval[2];
                    simplify(minimize(f, x = lowerbound .. upperbound))
                end proc,
                SemiAlgebraic(map(poly -> poly >= 0, basis), [x])));
$ifdef LOG_TIME
        END_LOG_TIME("minPolyOverBasis",0)
$endif
        return output;
    end proc;

# Find N such that
# - s + N g > 0 over L1 := SemiAlgebraic([op(S), s <= 0], [x]);
    findN := proc(s, f, t, g, basis)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("findN", 0)
$endif
    local min_s, locations, N;
        # This branch means that s is already strictly positive over S
        if evalb(SemiAlgebraic([op(map(poly -> poly >= 0, basis)), s <= 0], [x]) = []) then
$ifdef LOG_TIME
            END_LOG_TIME("findN",0)
$endif
            return 0;
        else
            min_s := minPolyOverBasis(s, basis, x);
            locations := [RealDomain:-solve](s = min_s);
            # If locations is empty then the equation `s = min_s` is trivial
            if evalb(locations = []) then
                N := ceil(-min_s/minPolyOverBasis(g, basis, x)+BUMP_FINDN);
            else
                N := ceil(-min_s/min(map(g, locations))+BUMP_FINDN);
            end if;
$ifdef LOG_TIME
            END_LOG_TIME("findN",0)
$endif
            return N;
        end if;
    end proc;

# Find positive rational eps so small
# such that
# - f > 0
# - 1 > eps*delta*f
# - eps*t1 + s1*f > 0
# over L2 := {}
    findEps := proc(delta, s1, f, t1, g, basis)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("findEps",0)
$endif
    local eps, top, bot, curr;
    local condition1, condition2, condition3;
    local _basis := map(poly -> poly >= 0, basis);
        top := -minPolyOverBasis(-g, basis, x);
        bot := 0;
        curr := (top+bot)/2;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Max bound for eps", top));
        condition1 := SemiAlgebraic([op(_basis), g <= curr, f <= 0], [x]) = [];
        condition2 := SemiAlgebraic([op(_basis), g <= curr, 1 <= curr*delta*f], [x]) = [];
        condition3 := SemiAlgebraic([op(_basis), g <= curr, curr*t1+s1*f <= 0], [x]) = [];
        while evalb(condition1 and condition2 and condition3) = false do
            top := curr;
            curr := (top + bot)/2;
            condition1 := SemiAlgebraic([op(_basis), g <= curr, f <= 0], [x]) = [];
            condition2 := SemiAlgebraic([op(_basis), g <= curr, 1 <= curr*delta*f], [x]) = [];
            condition3 := SemiAlgebraic([op(_basis), g <= curr, curr*t1+s1*f <= 0], [x]) = [];
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Searching eps", curr));
        end do;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> eps", eps));
$ifdef LOG_TIME
        END_LOG_TIME("findEps",0)
$endif
        return curr;
    end proc;

# Find k so large that
# - eps*t1 + s1*f > s1*f*(1-eps*delta*f)^k over the set { p \in C | g(p) \leq eps } =: L2
# - 1 > s1*f*(1-eps*delta*f)^k over the set { p \in C | g(p) \geq eps } =: L3
    findK := proc(eps, delta, s1, f, t1, g, basis, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("findK",0)
$endif
    local k := 0;
    local k_condition_1, k_condition_2;
$ifdef LOG_TIME
        START_LOG_TIME("findK::condition_1",1)
$endif
        k_condition_1 := SemiAlgebraic(
            [
                op(map(poly -> poly >= 0, basis)),
                g <= eps,
                eps*t1 + s1*f <= s1*f*(1-eps*delta*f)^k
            ], [x]) = [];

        while evalb(k_condition_1) = false do
            k := k+1;
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Searching k at first condition", k));
            k_condition_1 := SemiAlgebraic(
                [
                    op(map(poly -> poly >= 0, basis)),
                    g <= eps,
                    eps*t1 + s1*f <= s1*f*(1-eps*delta*f)^k
                ], [x]) = [];
        end do;
$ifdef LOG_TIME
        END_LOG_TIME("findK::condition_1",1)
$endif

$ifdef LOG_TIME
        START_LOG_TIME("findK::condition_2",2)
$endif
        k_condition_2 := SemiAlgebraic(
            [
                op(map(poly -> poly >= 0, basis)),
                g >= eps,
                1 <= s1*f*(1-eps*delta*f)^k
            ], [x]) = [];

        while evalb(k_condition_2) = false do
            k := k+1;
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Searching k at second condition", k));
            k_condition_2 := SemiAlgebraic(
                [
                    op(map(poly -> poly >= 0, basis)),
                    g >= eps,
                    1 <= s1*f*(1-eps*delta*f)^k
                ], [x]) = [];
        end do;
$ifdef LOG_TIME
        END_LOG_TIME("findK::condition_2",2)
$endif

$ifdef LOG_TIME
        END_LOG_TIME("findK",0)
$endif
        return k;
    end proc;

    lift := proc(f, g, basis, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("lift",0)
$endif

        ExtendedEuclideanAlgorithm(f, g, x, 's', 't');

    local N := findN(s, f, t, g, basis);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> N", N));

    local s1 := s + N*g;
    local t1 := t - N*f;

# Find positive rational d \in R[x] such that
# d*f*g < 1 on C
    local delta := -9/10/minPolyOverBasis(-f*g, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> delta", delta));

    local eps := findEps(delta, s1, f, t1, g, basis);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> eps", eps));
    local k := findK(eps, delta, s1, f, t1, g, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> k", k));

    local r := s1 * delta * f * sum((1 - delta*f*g)^i, i= 0 .. (k - 1));
    local sigma := s1 - r*g;
    local tau := t1 + r*f;

$ifdef LOG_TIME
        END_LOG_TIME("lift",0)
$endif
        return sigma, tau;
    end proc;

end module;
