maximize eps

st

eps >= 0
eps <= 1
f_3_1-f_1_1-1l0+1l1 = 0
eps-f_1_0+f_3_0+1000l0 <= 0
f_2_1-f_1_1-1l2-1l3 = 0
eps-f_1_0+f_2_0+1000l2 <= 0
-f_1_1-1l4 = 0
-f_1_0+1000l4 < 0
-f_2_1+1l5 = 0
-f_2_0+1l5 <= 0
-f_3_1-1l6 = 0
-f_3_0+1000l6 < 0

bounds

-inf<= f_1_0 <= +inf
-inf<= f_1_1 <= +inf
-inf<= f_2_0 <= +inf
-inf<= f_2_1 <= +inf
-inf<= f_3_0 <= +inf
-inf<= f_3_1 <= +inf
end
