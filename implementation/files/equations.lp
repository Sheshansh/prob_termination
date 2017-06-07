maximize eps1+eps2+eps3+eps4+eps5+eps6+eps7+eps8+eps9

st

eps1 >= 0
eps1 <= 1
eps2 >= 0
eps2 <= 1
eps3 >= 0
eps3 <= 1
eps4 >= 0
eps4 <= 1
eps5 >= 0
eps5 <= 1
eps6 >= 0
eps6 <= 1
eps7 >= 0
eps7 <= 1
eps8 >= 0
eps8 <= 1
eps9 >= 0
eps9 <= 1
f_3_1-f_1_1+1l0+1l1 = 0
eps1-f_1_0+f_3_0+1l0 <= 0
f_2_1-f_1_1+1l2-1l3 = 0
eps2-f_1_0+f_2_0+1l2 <= 0
f_4_1-f_3_1+1l4 = 0
eps3-f_3_0+f_4_0 <= 0
f_5_1-f_3_1+1l5 = 0
eps4-f_3_0+f_5_0 <= 0
0.875f_6_1+0.125f_7_1-f_4_1+1l6 = 0
eps5-f_4_0+0.875f_6_0+0.125f_7_0 <= 0
f_8_1-f_5_1+1l7 = 0
eps6-f_5_0+f_8_0 <= 0
-1f_1_1-f_6_1+1l8 = 0
eps7-f_6_0+f_1_0-1f_1_1 <= 0
1f_1_1-f_7_1+1l9 = 0
eps8-f_7_0+f_1_0+1f_1_1 <= 0
-1f_1_1-f_8_1+1l10 = 0
eps9-f_8_0+f_1_0-1f_1_1 <= 0
-f_1_1+1l11 = 0
-f_1_0+1l11 < 0
-f_2_1-1l12 = 0
-f_2_0 <= 0
-f_3_1+1l13 = 0
-f_3_0 < 0
-f_4_1+1l14 = 0
-f_4_0 < 0
-f_5_1+1l15 = 0
-f_5_0 < 0
-f_6_1+1l16 = 0
-f_6_0 < 0
-f_7_1+1l17 = 0
-f_7_0 < 0
-f_8_1+1l18 = 0
-f_8_0 < 0

bounds

-inf<= f_1_0 <= +inf
-inf<= f_1_1 <= +inf
-inf<= f_2_0 <= +inf
-inf<= f_2_1 <= +inf
-inf<= f_3_0 <= +inf
-inf<= f_3_1 <= +inf
-inf<= f_4_0 <= +inf
-inf<= f_4_1 <= +inf
-inf<= f_5_0 <= +inf
-inf<= f_5_1 <= +inf
-inf<= f_6_0 <= +inf
-inf<= f_6_1 <= +inf
-inf<= f_7_0 <= +inf
-inf<= f_7_1 <= +inf
-inf<= f_8_0 <= +inf
-inf<= f_8_1 <= +inf
end
