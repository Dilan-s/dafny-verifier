datatype DT_1<T_1> = DT_1_1 | DT_1_2(DT_1_2_1: T_1, DT_1_2_2: array<bool>, DT_1_2_3: T_1) | DT_1_3(DT_1_3_1: T_1, DT_1_3_2: T_1)
datatype DT_2 = DT_2_1
datatype DT_3 = DT_3_1 | DT_3_2
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: bool, p_m_method_9_2: bool, p_m_method_9_3: bool, p_m_method_9_4: bool) returns (ret_1: (bool, bool, int))
	requires ((p_m_method_9_4 == false) && (p_m_method_9_1 == false) && (p_m_method_9_3 == false) && (p_m_method_9_2 == true));
	ensures (((p_m_method_9_4 == false) && (p_m_method_9_1 == false) && (p_m_method_9_3 == false) && (p_m_method_9_2 == true)) ==> (((ret_1).0 == true) && ((ret_1).1 == false) && ((ret_1).2 == 10)));
{
	var v_bool_12: bool := false;
	var v_bool_13: bool := false;
	var v_bool_14: bool := true;
	var v_bool_15: bool := false;
	var v_bool_bool_int_2: (bool, bool, int) := m_method_10(v_bool_12, v_bool_13, v_bool_14, v_bool_15);
	print "v_bool_bool_int_2", " ", v_bool_bool_int_2, " ", "p_m_method_9_4", " ", p_m_method_9_4, " ", "p_m_method_9_3", " ", p_m_method_9_3, " ", "v_bool_15", " ", v_bool_15, " ", "v_bool_13", " ", v_bool_13, " ", "v_bool_14", " ", v_bool_14, " ", "p_m_method_9_2", " ", p_m_method_9_2, " ", "p_m_method_9_1", " ", p_m_method_9_1, " ", "v_bool_12", " ", v_bool_12, "\n";
	return v_bool_bool_int_2;
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: bool, p_m_method_8_2: bool, p_m_method_8_3: bool) returns (ret_1: seq<bool>)
	requires ((p_m_method_8_2 == true) && (p_m_method_8_1 == true) && (p_m_method_8_3 == false));
	ensures (((p_m_method_8_2 == true) && (p_m_method_8_1 == true) && (p_m_method_8_3 == false)) ==> (|ret_1| == 3 && (ret_1[0] == true) && (ret_1[1] == false) && (ret_1[2] == true)));
{
	var v_map_5: map<bool, seq<bool>> := map[false := [true, false], true := [true, false, true]];
	var v_bool_6: bool := true;
	print "v_map_5", " ", (v_map_5 == map[false := [true, false], true := [true, false, true]]), " ", "p_m_method_8_1", " ", p_m_method_8_1, " ", "p_m_method_8_3", " ", p_m_method_8_3, " ", "p_m_method_8_2", " ", p_m_method_8_2, " ", "v_bool_6", " ", v_bool_6, "\n";
	return (if ((v_bool_6 in v_map_5)) then (v_map_5[v_bool_6]) else ([false]));
}

method m_method_7(p_m_method_7_1: bool, p_m_method_7_2: DT_1<int>, p_m_method_7_3: seq<real>, p_m_method_7_4: bool) returns (ret_1: seq<(real, bool, bool)>)
{
	var v_real_bool_bool_1: (real, bool, bool) := (-8.01, false, false);
	return [v_real_bool_bool_1];
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: int, p_m_method_6_2: int, p_m_method_6_3: int, p_m_method_6_4: int) returns (ret_1: int)
	requires ((p_m_method_6_4 == 20) && (p_m_method_6_3 == 15) && (p_m_method_6_2 == 25) && (p_m_method_6_1 == 22));
	ensures (((p_m_method_6_4 == 20) && (p_m_method_6_3 == 15) && (p_m_method_6_2 == 25) && (p_m_method_6_1 == 22)) ==> ((ret_1 == 11)));
{
	print "p_m_method_6_3", " ", p_m_method_6_3, " ", "p_m_method_6_2", " ", p_m_method_6_2, " ", "p_m_method_6_4", " ", p_m_method_6_4, " ", "p_m_method_6_1", " ", p_m_method_6_1, "\n";
	return 11;
}

method m_method_5(p_m_method_5_1: map<int, int>, p_m_method_5_2: int, p_m_method_5_3: int) returns (ret_1: int)
	requires ((p_m_method_5_1 == map[5 := 9]) && (p_m_method_5_3 == 6) && (p_m_method_5_2 == 25));
	ensures (((p_m_method_5_1 == map[5 := 9]) && (p_m_method_5_3 == 6) && (p_m_method_5_2 == 25)) ==> ((ret_1 == 13)));
{
	print "p_m_method_5_3", " ", p_m_method_5_3, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", (p_m_method_5_1 == map[5 := 9]), "\n";
	return 13;
}

method m_method_4(p_m_method_4_1: int, p_m_method_4_2: int, p_m_method_4_3: int) returns (ret_1: int, ret_2: DT_1<int>, ret_3: int)
	requires ((p_m_method_4_2 == 0) && (p_m_method_4_1 == 10) && (p_m_method_4_3 == 29));
	ensures (((p_m_method_4_2 == 0) && (p_m_method_4_1 == 10) && (p_m_method_4_3 == 29)) ==> ((ret_1 == 11) && (ret_2.DT_1_3? && ((ret_2.DT_1_3_1 == 9) && (ret_2.DT_1_3_2 == 3))) && (ret_3 == 11)));
{
	var v_map_1: map<int, int> := map[5 := 9];
	var v_int_7: int := 25;
	var v_int_8: int := 6;
	var v_int_9: int := m_method_5(v_map_1, v_int_7, v_int_8);
	var v_int_10: int := 12;
	var v_int_11: int := 20;
	var v_int_12: int := safe_modulus(v_int_10, v_int_11);
	var v_int_13: int := 22;
	var v_int_14: int := 25;
	var v_int_15: int := 15;
	var v_int_16: int := 20;
	var v_int_17: int := m_method_6(v_int_13, v_int_14, v_int_15, v_int_16);
	var v_map_2: map<int, int> := map[5 := 26, 10 := 6, 19 := 10, 12 := -25, 6 := 9];
	var v_int_18: int := 20;
	var v_int_19: int := 11;
	var v_int_20: int := 28;
	var v_int_21: int := safe_modulus(v_int_19, v_int_20);
	v_int_20, v_int_7, v_int_12, v_int_14, v_int_18 := v_int_9, v_int_12, v_int_17, (if ((v_int_18 in v_map_2)) then (v_map_2[v_int_18]) else (9)), v_int_21;
	var v_DT_1_3_1: DT_1<int> := DT_1_3(9, 3);
	var v_DT_1_3_2: DT_1<int> := DT_1_3(7, 7);
	var v_DT_1_3_3: DT_1<int> := DT_1_3(-27, 5);
	var v_seq_3: seq<DT_1<int>> := [v_DT_1_3_1, v_DT_1_3_2, v_DT_1_3_3];
	var v_int_22: int := 9;
	var v_seq_42: seq<DT_1<int>> := v_seq_3;
	var v_int_69: int := v_int_22;
	var v_int_70: int := safe_index_seq(v_seq_42, v_int_69);
	v_int_22 := v_int_70;
	var v_DT_1_3_4: DT_1<int> := DT_1_3(9, 11);
	print "v_DT_1_3_4", " ", v_DT_1_3_4, " ", "v_DT_1_3_1", " ", v_DT_1_3_1, " ", "v_DT_1_3_3", " ", v_DT_1_3_3, " ", "v_DT_1_3_2", " ", v_DT_1_3_2, " ", "v_DT_1_3_3.DT_1_3_2", " ", v_DT_1_3_3.DT_1_3_2, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_DT_1_3_3.DT_1_3_1", " ", v_DT_1_3_3.DT_1_3_1, " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_int_9", " ", v_int_9, " ", "p_m_method_4_1", " ", p_m_method_4_1, " ", "v_int_20", " ", v_int_20, " ", "p_m_method_4_3", " ", p_m_method_4_3, " ", "p_m_method_4_2", " ", p_m_method_4_2, " ", "v_DT_1_3_2.DT_1_3_2", " ", v_DT_1_3_2.DT_1_3_2, " ", "v_DT_1_3_2.DT_1_3_1", " ", v_DT_1_3_2.DT_1_3_1, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[5 := 9]), " ", "v_map_2", " ", (v_map_2 == map[19 := 10, 5 := 26, 6 := 9, 10 := 6, 12 := -25]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_int_17", " ", v_int_17, " ", "v_DT_1_3_4.DT_1_3_1", " ", v_DT_1_3_4.DT_1_3_1, " ", "v_int_16", " ", v_int_16, " ", "v_seq_3", " ", v_seq_3, " ", "v_DT_1_3_4.DT_1_3_2", " ", v_DT_1_3_4.DT_1_3_2, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_DT_1_3_1.DT_1_3_2", " ", v_DT_1_3_1.DT_1_3_2, " ", "v_DT_1_3_1.DT_1_3_1", " ", v_DT_1_3_1.DT_1_3_1, "\n";
	return v_int_18, (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_22]) else (v_DT_1_3_4)), v_int_19;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: int, p_m_method_3_3: int, p_m_method_3_4: int) returns (ret_1: DT_1<real>)
	requires ((p_m_method_3_1 == 28) && (p_m_method_3_3 == 10) && (p_m_method_3_2 == 10) && (p_m_method_3_4 == 10));
	ensures (((p_m_method_3_1 == 28) && (p_m_method_3_3 == 10) && (p_m_method_3_2 == 10) && (p_m_method_3_4 == 10)) ==> ((ret_1.DT_1_2? && ((-18.16 < ret_1.DT_1_2_1 < -17.96) && ret_1.DT_1_2_2.Length == 5 && (ret_1.DT_1_2_2[0] == true) && (ret_1.DT_1_2_2[1] == true) && (ret_1.DT_1_2_2[2] == false) && (ret_1.DT_1_2_2[3] == false) && (ret_1.DT_1_2_2[4] == false) && (19.78 < ret_1.DT_1_2_3 < 19.98)))));
{
	assert ((p_m_method_3_2 == 10));
	expect ((p_m_method_3_2 == 10));
	var v_int_23: int := p_m_method_3_3;
	var v_int_24: int := (8 % -1);
	var v_int_25: int := (if (true) then (29) else (18));
	var v_int_26: int, v_DT_1_3_5: DT_1<int>, v_int_27: int := m_method_4(v_int_23, v_int_24, v_int_25);
	v_int_24, v_DT_1_3_5, v_int_26 := v_int_26, v_DT_1_3_5, v_int_27;
	var v_int_28: int := (match 27 {
		case 9 => 23
		case _ => 17
	});
	var v_int_29: int := (10 / 22);
	while (v_int_28 < v_int_29) 
		decreases v_int_29 - v_int_28;
		invariant (v_int_28 <= v_int_29) && ((((v_int_28 == 17)) ==> ((((v_int_25 == 29)) && ((v_int_27 == 11)) && ((v_int_26 == 11))))));
	{
		v_int_28 := (v_int_28 + 1);
		var v_map_3: map<int, int> := map[24 := 28, 0 := 14, 7 := 27];
		var v_int_30: int := 12;
		var v_int_31: int := 5;
		var v_int_32: int := m_method_5(v_map_3, v_int_30, v_int_31);
		v_int_26, v_int_25, v_int_27 := p_m_method_3_3, v_int_24, v_int_32;
		var v_map_4: map<bool, int> := map[true := 26, true := 22, true := 29, true := 14];
		var v_bool_3: bool := false;
		var v_array_2: array<bool> := new bool[4];
		v_array_2[0] := true;
		v_array_2[1] := true;
		v_array_2[2] := true;
		v_array_2[3] := true;
		var v_DT_1_2_3: DT_1<real> := DT_1_2(24.99, v_array_2, -12.71);
		var v_array_3: array<bool> := new bool[3] [true, false, true];
		var v_DT_1_2_4: DT_1<real> := DT_1_2(23.12, v_array_3, -15.08);
		var v_int_33: int, v_int_34: int, v_DT_1_2_5: DT_1<real> := (12 * 10), (if ((v_bool_3 in v_map_4)) then (v_map_4[v_bool_3]) else (9)), (match false {
			case _ => v_DT_1_2_4
		});
		var v_seq_4: seq<char> := (match 'n' {
			case _ => []
		});
		var v_array_4: array<seq<real>> := new seq<real>[5] [[], [26.94, 18.84], [9.24], [-0.42, -13.37], []];
		var v_array_5: array<seq<real>> := new seq<real>[3] [[-19.78], [-15.66, 16.94, 6.34, 14.01], [-28.58]];
		var v_seq_5: seq<array<seq<real>>> := [v_array_4, v_array_5];
		var v_int_35: int := 27;
		var v_array_6: array<seq<real>> := new seq<real>[3] [[], [21.17, 14.59, 22.94], [-14.12, -6.68]];
		var v_seq_6: seq<seq<seq<int>>> := [];
		var v_int_36: int := 2;
		var v_bool_4: bool := false;
		var v_DT_1_3_6: DT_1<int> := DT_1_3(-15, 25);
		var v_DT_1_3_7: DT_1<int> := v_DT_1_3_6;
		var v_seq_7: seq<real> := [5.18, -5.41, -11.55, 13.95];
		var v_bool_5: bool := false;
		var v_seq_8: seq<(real, bool, bool)> := m_method_7(v_bool_4, v_DT_1_3_7, v_seq_7, v_bool_5);
		var v_array_7: array<seq<real>>, v_seq_9: seq<int>, v_seq_10: seq<seq<int>>, v_seq_11: seq<(real, bool, bool)> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_35]) else (v_array_6)), ([23] + [1, 0, 22]), (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_36]) else ([[11, 15, -13, 14], [1, 17, 1, 4]])), v_seq_8;
		var v_array_8: array<bool> := new bool[5];
		v_array_8[0] := false;
		v_array_8[1] := true;
		v_array_8[2] := false;
		v_array_8[3] := true;
		v_array_8[4] := false;
		var v_DT_1_2_6: DT_1<real> := DT_1_2(-16.70, v_array_8, -25.57);
		var v_array_9: array<bool> := new bool[5] [true, true, true, true, true];
		var v_DT_1_2_7: DT_1<real> := DT_1_2(-22.68, v_array_9, -12.14);
		var v_array_10: array<bool> := new bool[3] [false, true, true];
		var v_DT_1_2_8: DT_1<real> := DT_1_2(-22.72, v_array_10, 24.22);
		return (match true {
			case _ => v_DT_1_2_8
		});
	}
	var v_array_11: array<bool> := new bool[5] [true, true, false, false, false];
	var v_DT_1_2_9: DT_1<real> := DT_1_2(-18.06, v_array_11, 19.88);
	var v_array_12: array<bool> := new bool[3] [false, false, false];
	var v_DT_1_2_10: DT_1<real> := DT_1_2(-11.86, v_array_12, -0.96);
	var v_seq_12: seq<DT_1<real>> := [v_DT_1_2_9, v_DT_1_2_10];
	var v_int_37: int := 26;
	var v_seq_43: seq<DT_1<real>> := v_seq_12;
	var v_int_71: int := v_int_37;
	var v_int_72: int := safe_index_seq(v_seq_43, v_int_71);
	v_int_37 := v_int_72;
	var v_array_13: array<bool> := new bool[4] [true, false, true, true];
	var v_DT_1_2_11: DT_1<real> := DT_1_2(15.86, v_array_13, 27.56);
	var v_DT_1_2_21: DT_1<real> := DT_1_2(-18.06, v_array_11, 19.88);
	var v_DT_1_2_22: DT_1<real> := DT_1_2(-18.06, v_array_11, 19.88);
	var v_DT_1_2_23: DT_1<real> := DT_1_2(-11.86, v_array_12, -0.96);
	var v_DT_1_2_24: DT_1<real> := DT_1_2(15.86, v_array_13, 27.56);
	var v_DT_1_2_25: DT_1<real> := DT_1_2(-11.86, v_array_12, -0.96);
	print "v_DT_1_3_5", " ", v_DT_1_3_5, " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_array_11[4]", " ", v_array_11[4], " ", "v_array_13[0]", " ", v_array_13[0], " ", "v_array_11[2]", " ", v_array_11[2], " ", "v_array_12[1]", " ", v_array_12[1], " ", "v_array_13[2]", " ", v_array_13[2], " ", "v_array_11[0]", " ", v_array_11[0], " ", "v_DT_1_2_9.DT_1_2_1", " ", (v_DT_1_2_9.DT_1_2_1 == -18.06), " ", "v_DT_1_2_9.DT_1_2_2", " ", (v_DT_1_2_9.DT_1_2_2 == v_array_11), " ", "v_DT_1_2_9.DT_1_2_3", " ", (v_DT_1_2_9.DT_1_2_3 == 19.88), " ", "v_DT_1_2_9", " ", (v_DT_1_2_9 == v_DT_1_2_21), " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_seq_12", " ", (v_seq_12 == [v_DT_1_2_22, v_DT_1_2_23]), " ", "v_int_25", " ", v_int_25, " ", "v_DT_1_2_10.DT_1_2_3", " ", (v_DT_1_2_10.DT_1_2_3 == -0.96), " ", "v_DT_1_2_10.DT_1_2_2", " ", (v_DT_1_2_10.DT_1_2_2 == v_array_12), " ", "v_DT_1_2_10.DT_1_2_1", " ", (v_DT_1_2_10.DT_1_2_1 == -11.86), " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", p_m_method_3_4, " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "p_m_method_3_3", " ", p_m_method_3_3, " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_array_13[1]", " ", v_array_13[1], " ", "v_array_13[3]", " ", v_array_13[3], " ", "v_array_11[3]", " ", v_array_11[3], " ", "v_array_12[2]", " ", v_array_12[2], " ", "v_array_11[1]", " ", v_array_11[1], " ", "v_array_12[0]", " ", v_array_12[0], " ", "v_int_29", " ", v_int_29, " ", "v_DT_1_2_11.DT_1_2_2", " ", (v_DT_1_2_11.DT_1_2_2 == v_array_13), " ", "v_DT_1_2_11.DT_1_2_1", " ", (v_DT_1_2_11.DT_1_2_1 == 15.86), " ", "v_DT_1_2_11.DT_1_2_3", " ", (v_DT_1_2_11.DT_1_2_3 == 27.56), " ", "v_int_37", " ", v_int_37, " ", "v_DT_1_2_11", " ", (v_DT_1_2_11 == v_DT_1_2_24), " ", "v_DT_1_2_10", " ", (v_DT_1_2_10 == v_DT_1_2_25), "\n";
	return (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_37]) else (v_DT_1_2_11));
}

method safe_division(p_safe_division_1: int, p_safe_division_2: int) returns (ret_1: int)
	ensures (p_safe_division_2 == 0 ==> ret_1 == p_safe_division_1) && (p_safe_division_2 != 0 ==> ret_1 == p_safe_division_1 / p_safe_division_2);
{
	return (if ((p_safe_division_2 != 0)) then ((p_safe_division_1 / p_safe_division_2)) else (p_safe_division_1));
}

method safe_subsequence(p_safe_subsequence_1: seq, p_safe_subsequence_2: int, p_safe_subsequence_3: int) returns (ret_1: int, ret_2: int)
	ensures ((|p_safe_subsequence_1| > 0) ==> ((0 <= ret_1 < |p_safe_subsequence_1|) && (0 <= ret_2 < |p_safe_subsequence_1|) && ret_1 <= ret_2)) && ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_2 == 0))) || ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_2 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)))));
{
	var v_seq_1: seq := p_safe_subsequence_1;
	var v_int_2: int := p_safe_subsequence_2;
	var v_int_3: int := safe_index_seq(v_seq_1, v_int_2);
	var v_int_1: int := v_int_3;
	var v_seq_2: seq := p_safe_subsequence_1;
	var v_int_5: int := p_safe_subsequence_3;
	var v_int_6: int := safe_index_seq(v_seq_2, v_int_5);
	var v_int_4: int := v_int_6;
	if (v_int_1 <= v_int_4) {
		return v_int_1, v_int_4;
	} else {
		return v_int_4, v_int_1;
	}
}

method m_method_2(p_m_method_2_1: DT_1<real>) returns (ret_1: bool)
	requires ((p_m_method_2_1.DT_1_2? && ((24.10 < p_m_method_2_1.DT_1_2_1 < 24.30) && p_m_method_2_1.DT_1_2_2.Length == 3 && (p_m_method_2_1.DT_1_2_2[0] == true) && (p_m_method_2_1.DT_1_2_2[1] == false) && (p_m_method_2_1.DT_1_2_2[2] == true) && (-18.39 < p_m_method_2_1.DT_1_2_3 < -18.19)))) || ((p_m_method_2_1.DT_1_2? && ((17.86 < p_m_method_2_1.DT_1_2_1 < 18.06) && p_m_method_2_1.DT_1_2_2.Length == 4 && (p_m_method_2_1.DT_1_2_2[0] == false) && (p_m_method_2_1.DT_1_2_2[1] == true) && (p_m_method_2_1.DT_1_2_2[2] == true) && (p_m_method_2_1.DT_1_2_2[3] == true) && (-26.44 < p_m_method_2_1.DT_1_2_3 < -26.24))));
	ensures (((p_m_method_2_1.DT_1_2? && ((17.86 < p_m_method_2_1.DT_1_2_1 < 18.06) && p_m_method_2_1.DT_1_2_2.Length == 4 && (p_m_method_2_1.DT_1_2_2[0] == false) && (p_m_method_2_1.DT_1_2_2[1] == true) && (p_m_method_2_1.DT_1_2_2[2] == true) && (p_m_method_2_1.DT_1_2_2[3] == true) && (-26.44 < p_m_method_2_1.DT_1_2_3 < -26.24)))) ==> ((ret_1 == false))) && (((p_m_method_2_1.DT_1_2? && ((24.10 < p_m_method_2_1.DT_1_2_1 < 24.30) && p_m_method_2_1.DT_1_2_2.Length == 3 && (p_m_method_2_1.DT_1_2_2[0] == true) && (p_m_method_2_1.DT_1_2_2[1] == false) && (p_m_method_2_1.DT_1_2_2[2] == true) && (-18.39 < p_m_method_2_1.DT_1_2_3 < -18.19)))) ==> ((ret_1 == false)));
{
	print "p_m_method_2_1.DT_1_2_2[1]", " ", p_m_method_2_1.DT_1_2_2[1], " ", "p_m_method_2_1.DT_1_2_2", " ", "p_m_method_2_1", " ", "p_m_method_2_1.DT_1_2_1", " ", (p_m_method_2_1.DT_1_2_1 == 17.96), " ", "p_m_method_2_1.DT_1_2_2[0]", " ", p_m_method_2_1.DT_1_2_2[0], " ", "p_m_method_2_1.DT_1_2_2[2]", " ", p_m_method_2_1.DT_1_2_2[2], " ", "p_m_method_2_1.DT_1_2_3", " ", (p_m_method_2_1.DT_1_2_3 == -26.34), "\n";
	return false;
}

method m_method_1(p_m_method_1_1: seq<int>, p_m_method_1_2: seq<bool>, p_m_method_1_3: (bool, bool, int)) returns (ret_1: DT_1<real>)
	requires (|p_m_method_1_1| == 0 && ((p_m_method_1_3).0 == true) && ((p_m_method_1_3).1 == false) && ((p_m_method_1_3).2 == 10) && |p_m_method_1_2| == 3 && (p_m_method_1_2[0] == true) && (p_m_method_1_2[1] == false) && (p_m_method_1_2[2] == true));
	ensures ((|p_m_method_1_1| == 0 && ((p_m_method_1_3).0 == true) && ((p_m_method_1_3).1 == false) && ((p_m_method_1_3).2 == 10) && |p_m_method_1_2| == 3 && (p_m_method_1_2[0] == true) && (p_m_method_1_2[1] == false) && (p_m_method_1_2[2] == true)) ==> ((ret_1.DT_1_2? && ((-18.16 < ret_1.DT_1_2_1 < -17.96) && ret_1.DT_1_2_2.Length == 5 && (ret_1.DT_1_2_2[0] == true) && (ret_1.DT_1_2_2[1] == true) && (ret_1.DT_1_2_2[2] == false) && (ret_1.DT_1_2_2[3] == false) && (ret_1.DT_1_2_2[4] == false) && (19.78 < ret_1.DT_1_2_3 < 19.98)))));
{
	if true {
		assert ((p_m_method_1_1 == []) && (p_m_method_1_3.0 == true) && (p_m_method_1_3.1 == false));
		expect ((p_m_method_1_1 == []) && (p_m_method_1_3.0 == true) && (p_m_method_1_3.1 == false));
		var v_array_1: array<bool> := new bool[3] [true, false, true];
		var v_DT_1_2_1: DT_1<real> := DT_1_2(24.20, v_array_1, -18.29);
		var v_DT_1_2_2: DT_1<real> := v_DT_1_2_1;
		var v_bool_1: bool := m_method_2(v_DT_1_2_2);
		var v_bool_2: bool, v_real_1: real := (false ==> v_bool_1), v_DT_1_2_1.DT_1_2_1;
		var v_DT_1_2_19: DT_1<real> := DT_1_2(24.20, v_array_1, -18.29);
		var v_DT_1_2_20: DT_1<real> := DT_1_2(24.20, v_array_1, -18.29);
		print "v_bool_1", " ", v_bool_1, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_1_2_2", " ", (v_DT_1_2_2 == v_DT_1_2_19), " ", "v_DT_1_2_1", " ", (v_DT_1_2_1 == v_DT_1_2_20), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_real_1", " ", (v_real_1 == 24.20), " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_DT_1_2_1.DT_1_2_1", " ", (v_DT_1_2_1.DT_1_2_1 == 24.20), " ", "v_DT_1_2_1.DT_1_2_2", " ", (v_DT_1_2_1.DT_1_2_2 == v_array_1), " ", "v_DT_1_2_1.DT_1_2_3", " ", (v_DT_1_2_1.DT_1_2_3 == -18.29), " ", "p_m_method_1_3.0", " ", p_m_method_1_3.0, " ", "p_m_method_1_3.1", " ", p_m_method_1_3.1, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "p_m_method_1_3.2", " ", p_m_method_1_3.2, " ", "p_m_method_1_3", " ", p_m_method_1_3, "\n";
	}
	var v_int_38: int := (match false {
		case false => 28
		case _ => -3
	});
	var v_int_39: int := p_m_method_1_3.2;
	var v_int_40: int := p_m_method_1_3.2;
	var v_int_41: int := p_m_method_1_3.2;
	var v_DT_1_2_12: DT_1<real> := m_method_3(v_int_38, v_int_39, v_int_40, v_int_41);
	print "p_m_method_1_3.0", " ", p_m_method_1_3.0, " ", "p_m_method_1_3.1", " ", p_m_method_1_3.1, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_int_39", " ", v_int_39, " ", "v_int_38", " ", v_int_38, " ", "p_m_method_1_3.2", " ", p_m_method_1_3.2, " ", "v_DT_1_2_12", " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, "\n";
	return v_DT_1_2_12;
}

method m_method_10(p_m_method_10_1: bool, p_m_method_10_2: bool, p_m_method_10_3: bool, p_m_method_10_4: bool) returns (ret_1: (bool, bool, int))
	requires ((p_m_method_10_4 == false) && (p_m_method_10_2 == false) && (p_m_method_10_3 == true) && (p_m_method_10_1 == false));
	ensures (((p_m_method_10_4 == false) && (p_m_method_10_2 == false) && (p_m_method_10_3 == true) && (p_m_method_10_1 == false)) ==> (((ret_1).0 == true) && ((ret_1).1 == false) && ((ret_1).2 == 10)));
{
	var v_bool_11: bool := true;
	var v_bool_bool_int_1: (bool, bool, int) := (true, false, 10);
	print "p_m_method_10_3", " ", p_m_method_10_3, " ", "v_bool_bool_int_1.1", " ", v_bool_bool_int_1.1, " ", "p_m_method_10_4", " ", p_m_method_10_4, " ", "v_bool_bool_int_1", " ", v_bool_bool_int_1, " ", "v_bool_bool_int_1.0", " ", v_bool_bool_int_1.0, " ", "v_bool_bool_int_1.2", " ", v_bool_bool_int_1.2, " ", "v_bool_11", " ", v_bool_11, " ", "p_m_method_10_1", " ", p_m_method_10_1, " ", "p_m_method_10_2", " ", p_m_method_10_2, "\n";
	return v_bool_bool_int_1;
}

method m_method_11(p_m_method_11_1: (int, bool), p_m_method_11_2: map<bool, int>, p_m_method_11_3: map<int, int>, p_m_method_11_4: char) returns (ret_1: char)
	requires ((p_m_method_11_3 == map[18 := -28, 22 := 28, 24 := 0, 26 := 10, 11 := 16]) && (p_m_method_11_4 == 'f') && ((p_m_method_11_1).0 == -13) && ((p_m_method_11_1).1 == true) && (p_m_method_11_2 == map[false := -13, true := 0])) || ((p_m_method_11_3 == map[-4 := 25, 22 := -14]) && (p_m_method_11_4 == 'j') && ((p_m_method_11_1).0 == 14) && ((p_m_method_11_1).1 == false) && (p_m_method_11_2 == map[false := -5, true := 27]));
	ensures (((p_m_method_11_3 == map[18 := -28, 22 := 28, 24 := 0, 26 := 10, 11 := 16]) && (p_m_method_11_4 == 'f') && ((p_m_method_11_1).0 == -13) && ((p_m_method_11_1).1 == true) && (p_m_method_11_2 == map[false := -13, true := 0])) ==> ((ret_1 == 'u'))) && (((p_m_method_11_3 == map[-4 := 25, 22 := -14]) && (p_m_method_11_4 == 'j') && ((p_m_method_11_1).0 == 14) && ((p_m_method_11_1).1 == false) && (p_m_method_11_2 == map[false := -5, true := 27])) ==> ((ret_1 == 'u')));
{
	var v_int_bool_5: (int, bool) := (-13, true);
	var v_int_bool_6: (int, bool) := (14, false);
	assert ((p_m_method_11_1.0 == -13) && (p_m_method_11_2 == map[false := -13, true := 0]) && (p_m_method_11_4 == 'f') && (p_m_method_11_1 == v_int_bool_5)) || ((p_m_method_11_1.0 == 14) && (p_m_method_11_2 == map[false := -5, true := 27]) && (p_m_method_11_4 == 'j') && (p_m_method_11_1 == v_int_bool_6));
	expect ((p_m_method_11_1.0 == -13) && (p_m_method_11_2 == map[false := -13, true := 0]) && (p_m_method_11_4 == 'f') && (p_m_method_11_1 == v_int_bool_5)) || ((p_m_method_11_1.0 == 14) && (p_m_method_11_2 == map[false := -5, true := 27]) && (p_m_method_11_4 == 'j') && (p_m_method_11_1 == v_int_bool_6));
	print "p_m_method_11_1.0", " ", p_m_method_11_1.0, " ", "p_m_method_11_4", " ", (p_m_method_11_4 == 'f'), " ", "p_m_method_11_2", " ", (p_m_method_11_2 == map[false := -13, true := 0]), " ", "p_m_method_11_1.1", " ", p_m_method_11_1.1, " ", "p_m_method_11_3", " ", (p_m_method_11_3 == map[18 := -28, 22 := 28, 24 := 0, 26 := 10, 11 := 16]), " ", "p_m_method_11_1", " ", p_m_method_11_1, "\n";
	return 'u';
}

method m_method_12(p_m_method_12_1: seq<real>, p_m_method_12_2: char) returns (ret_1: seq<array<int>>)
	requires ((p_m_method_12_2 == 'u') && |p_m_method_12_1| == 4 && (-11.60 < p_m_method_12_1[0] < -11.40) && (29.73 < p_m_method_12_1[1] < 29.93) && (21.15 < p_m_method_12_1[2] < 21.35) && (24.98 < p_m_method_12_1[3] < 25.18)) || ((p_m_method_12_2 == 'J') && |p_m_method_12_1| == 3 && (-3.32 < p_m_method_12_1[0] < -3.12) && (21.13 < p_m_method_12_1[1] < 21.33) && (-21.10 < p_m_method_12_1[2] < -20.90));
	ensures (((p_m_method_12_2 == 'J') && |p_m_method_12_1| == 3 && (-3.32 < p_m_method_12_1[0] < -3.12) && (21.13 < p_m_method_12_1[1] < 21.33) && (-21.10 < p_m_method_12_1[2] < -20.90)) ==> (|ret_1| == 1 && ret_1[0].Length == 5 && (ret_1[0][0] == 25) && (ret_1[0][1] == 2) && (ret_1[0][2] == 18) && (ret_1[0][3] == 21) && (ret_1[0][4] == 12))) && (((p_m_method_12_2 == 'u') && |p_m_method_12_1| == 4 && (-11.60 < p_m_method_12_1[0] < -11.40) && (29.73 < p_m_method_12_1[1] < 29.93) && (21.15 < p_m_method_12_1[2] < 21.35) && (24.98 < p_m_method_12_1[3] < 25.18)) ==> (|ret_1| == 1 && ret_1[0].Length == 5 && (ret_1[0][0] == 25) && (ret_1[0][1] == 2) && (ret_1[0][2] == 18) && (ret_1[0][3] == 21) && (ret_1[0][4] == 12)));
{
	var v_array_20: array<int> := new int[5] [25, 2, 18, 21, 12];
	var v_array_21: array<int> := new int[4] [16, 9, 17, 8];
	var v_array_22: array<int> := new int[5] [1, 24, 27, -6, 12];
	var v_seq_32: seq<array<int>> := [v_array_20, v_array_21, v_array_22];
	var v_seq_49: seq<array<int>> := v_seq_32;
	var v_int_89: int := 1;
	var v_int_90: int := 16;
	var v_int_91: int, v_int_92: int := safe_subsequence(v_seq_49, v_int_89, v_int_90);
	var v_int_87: int, v_int_88: int := v_int_91, v_int_92;
	print "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_array_20", " ", (v_array_20 == v_array_20), " ", "v_array_20[0]", " ", v_array_20[0], " ", "v_array_20[1]", " ", v_array_20[1], " ", "v_array_21[0]", " ", v_array_21[0], " ", "v_array_20[2]", " ", v_array_20[2], " ", "v_array_21[1]", " ", v_array_21[1], " ", "v_array_22[0]", " ", v_array_22[0], " ", "v_array_20[3]", " ", v_array_20[3], " ", "v_array_21[2]", " ", v_array_21[2], " ", "v_array_22[1]", " ", v_array_22[1], " ", "v_array_20[4]", " ", v_array_20[4], " ", "v_array_21[3]", " ", v_array_21[3], " ", "v_array_22[2]", " ", v_array_22[2], " ", "v_array_22[3]", " ", v_array_22[3], " ", "v_array_22[4]", " ", v_array_22[4], " ", "p_m_method_12_1", " ", (p_m_method_12_1 == [-3.22, 21.23, -21.00]), " ", "p_m_method_12_2", " ", (p_m_method_12_2 == 'J'), " ", "v_seq_32", " ", (v_seq_32 == [v_array_20, v_array_21, v_array_22]), "\n";
	return (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_87..v_int_88]) else (v_seq_32));
}

method Main() returns ()
{
	var v_seq_13: seq<int> := [-5, 20];
	var v_seq_14: seq<int> := v_seq_13;
	var v_int_42: int := 23;
	var v_int_43: int := safe_index_seq(v_seq_14, v_int_42);
	var v_int_44: int := v_int_43;
	var v_seq_15: seq<int> := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_44 := 3]) else (v_seq_13));
	var v_seq_41: seq<int> := v_seq_15;
	var v_int_65: int := v_int_42;
	var v_int_66: int := 0;
	var v_int_67: int, v_int_68: int := safe_subsequence(v_seq_41, v_int_65, v_int_66);
	var v_int_63: int, v_int_64: int := v_int_67, v_int_68;
	var v_seq_17: seq<int> := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_63..v_int_64]) else (v_seq_15));
	var v_map_6: map<bool, bool> := map[true := true, false := false];
	var v_bool_7: bool := true;
	var v_bool_8: bool := (if ((v_bool_7 in v_map_6)) then (v_map_6[v_bool_7]) else (false));
	var v_bool_9: bool := (false <==> false);
	var v_bool_10: bool := (if (false) then (false) else (false));
	var v_seq_16: seq<bool> := m_method_8(v_bool_8, v_bool_9, v_bool_10);
	var v_seq_18: seq<bool> := v_seq_16;
	var v_array_14: array<bool> := new bool[4] [false, true, true, true];
	var v_DT_1_2_13: DT_1<real> := DT_1_2(17.96, v_array_14, -26.34);
	var v_DT_1_2_14: DT_1<real> := v_DT_1_2_13;
	var v_bool_16: bool := m_method_2(v_DT_1_2_14);
	var v_bool_17: bool := v_bool_16;
	var v_bool_18: bool := (false in map[true := true, false := true]);
	var v_bool_19: bool := (true <==> false);
	var v_bool_20: bool := !(true);
	var v_bool_bool_int_3: (bool, bool, int) := m_method_9(v_bool_17, v_bool_18, v_bool_19, v_bool_20);
	var v_bool_bool_int_4: (bool, bool, int) := v_bool_bool_int_3;
	var v_DT_1_2_15: DT_1<real> := m_method_1(v_seq_17, v_seq_18, v_bool_bool_int_4);
	var v_seq_19: seq<bool> := [false, true];
	var v_int_45: int := 25;
	var v_seq_20: seq<bool> := [false, false];
	var v_int_46: int := 8;
	var v_seq_44: seq<bool> := v_seq_20;
	var v_int_73: int := v_int_46;
	var v_int_74: int := safe_index_seq(v_seq_44, v_int_73);
	v_int_46 := v_int_74;
	var v_seq_21: seq<multiset<bool>> := [];
	var v_seq_22: seq<multiset<bool>> := (if ((|v_seq_21| > 0)) then (v_seq_21[19..13]) else (v_seq_21));
	var v_int_47: int := v_int_46;
	var v_seq_23: seq<set<char>> := ([{'t', 'E', 'X'}, {'M'}] + [{'U', 'A', 'R'}, {'C', 'j', 'O', 'J'}]);
	var v_array_15: array<real> := new real[5] [6.96, 24.42, 15.16, 9.73, 2.13];
	var v_int_48: int := v_array_15.Length;
	var v_seq_45: seq<set<char>> := v_seq_23;
	var v_int_75: int := v_int_48;
	var v_int_76: int := safe_index_seq(v_seq_45, v_int_75);
	v_int_48 := v_int_76;
	var v_seq_24: seq<bool> := [false, true, true, true];
	var v_int_49: int := -19;
	var v_seq_46: seq<bool> := v_seq_24;
	var v_int_77: int := v_int_49;
	var v_int_78: int := safe_index_seq(v_seq_46, v_int_77);
	v_int_49 := v_int_78;
	var v_map_7: map<char, multiset<real>> := map['t' := multiset({-21.16, 27.93, 20.25, 7.94}), 'W' := multiset{}, 'X' := multiset{-5.25}, 'u' := multiset{10.08, -23.15, 7.12}];
	var v_char_1: char := 'J';
	var v_DT_1_2_16: DT_1<real>, v_bool_21: bool, v_set_1: set<char>, v_multiset_1: multiset<real> := v_DT_1_2_15, ((if ((true && false)) then ((if ((|v_seq_19| > 0)) then (v_seq_19[v_int_45]) else (true))) else ((if ((|v_seq_20| > 0)) then (v_seq_20[v_int_46]) else (false)))) !in (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_47]) else ((multiset({false, true, true}) - multiset({false, true}))))), (match true {
		case true => (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_48]) else (({} + {'U', 'w', 'X', 'x'})))
		case _ => ((match 'V' {
			case _ => {'U', 'R', 'I'}
		}) + (map[24 := 'X', 1 := 'T', -3 := 'Y', 8 := 'g', 4 := 'H']).Values)
	}), ((if ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_49]) else (true))) then ((match 2 {
		case _ => multiset{20.62, -19.59, -7.80, -4.46}
	})) else ((multiset({-9.68, -11.26}) * multiset({-11.16, 3.49})))) * ((multiset{-20.23, 7.40, 7.40} - multiset({15.85, -16.22, 0.10})) * (if ((v_char_1 in v_map_7)) then (v_map_7[v_char_1]) else (multiset{26.28, -26.78, 11.26}))));
	var v_seq_26: seq<char> := (if (v_bool_21) then ((['u', 'e'] + ['t'])) else ((if (true) then (['n', 'J', 'W']) else (['z', 'p', 'F']))));
	var v_seq_25: seq<int> := [];
	var v_int_50: int := 4;
	var v_int_51: int := (if (v_bool_18) then ((match 28 {
		case 10 => 8
		case _ => 8
	})) else ((if ((|v_seq_25| > 0)) then (v_seq_25[v_int_50]) else (29))));
	var v_seq_50: seq<char> := v_seq_26;
	var v_int_93: int := v_int_51;
	var v_int_94: int := safe_index_seq(v_seq_50, v_int_93);
	v_int_51 := v_int_94;
	var v_int_bool_1: (int, bool) := (-13, true);
	var v_int_bool_2: (int, bool) := v_int_bool_1;
	var v_map_8: map<bool, int> := map[true := 0, false := -13];
	var v_map_9: map<int, int> := map[11 := 16, 22 := 28, 24 := 0, 26 := 10, 18 := -28];
	var v_char_2: char := 'f';
	var v_char_3: char := m_method_11(v_int_bool_2, v_map_8, v_map_9, v_char_2);
	var v_map_10: map<char, bool> := map['A' := false, 'H' := false];
	var v_char_4: char := 'Q';
	var v_seq_27: seq<multiset<multiset<bool>>> := [multiset{multiset({false}), multiset{true, true}}, multiset{multiset{true, true}, multiset({false, false}), multiset{false, false, true, true}, multiset({})}, multiset{}];
	var v_seq_28: seq<multiset<multiset<bool>>> := v_seq_27;
	var v_int_52: int := 15;
	var v_int_53: int := safe_index_seq(v_seq_28, v_int_52);
	var v_int_54: int := v_int_53;
	var v_seq_30: seq<multiset<multiset<bool>>> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_54 := multiset{multiset{false, false}, multiset{true, true, true, false}}]) else (v_seq_27));
	var v_seq_48: seq<multiset<multiset<bool>>> := v_seq_30;
	var v_seq_29: seq<int> := [25, 0, -11];
	var v_int_55: int := 20;
	var v_seq_47: seq<int> := v_seq_29;
	var v_int_79: int := v_int_55;
	var v_int_80: int := safe_index_seq(v_seq_47, v_int_79);
	v_int_55 := v_int_80;
	var v_int_83: int := (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_55]) else (-16));
	var v_int_84: int := 0;
	var v_int_85: int, v_int_86: int := safe_subsequence(v_seq_48, v_int_83, v_int_84);
	var v_int_81: int, v_int_82: int := v_int_85, v_int_86;
	var v_seq_31: seq<multiset<multiset<bool>>> := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_81..v_int_82]) else (v_seq_30));
	var v_int_56: int := v_int_51;
	var v_array_16: array<seq<int>> := new seq<int>[4] [[15], [26, 11, 2, 6], [15, 5, 5], [7, 0, 26]];
	var v_array_17: array<seq<int>> := new seq<int>[5];
	v_array_17[0] := [28, 16, 26];
	v_array_17[1] := [24, 14, -4, 16];
	v_array_17[2] := [5, 7, 0, 3];
	v_array_17[3] := [25, 5, 5];
	v_array_17[4] := [23, 25, 19, 3];
	var v_map_11: map<array<seq<int>>, multiset<multiset<bool>>> := map[v_array_16 := multiset{multiset{false, false, false, true}, multiset{true, false, true}}, v_array_17 := multiset({multiset{false}, multiset{false, false}})];
	var v_array_18: array<seq<int>> := new seq<int>[3];
	v_array_18[0] := [15, 2, 20];
	v_array_18[1] := [10, 9];
	v_array_18[2] := [3];
	var v_array_19: array<seq<int>> := v_array_18;
	var v_seq_33: seq<real> := (if (true) then ([-3.22, 21.23, -21.00]) else ([28.63, 19.48]));
	var v_char_5: char := v_char_1;
	var v_seq_34: seq<array<int>> := m_method_12(v_seq_33, v_char_5);
	var v_seq_35: seq<real> := (if (true) then ([-11.50, 29.83, 21.25, 25.08]) else ([18.93, 27.64]));
	var v_int_bool_3: (int, bool) := (14, false);
	var v_int_bool_4: (int, bool) := v_int_bool_3;
	var v_map_12: map<bool, int> := map[true := 27, false := -5];
	var v_map_13: map<int, int> := map[22 := -14, -4 := 25];
	var v_char_6: char := 'j';
	var v_char_7: char := m_method_11(v_int_bool_4, v_map_12, v_map_13, v_char_6);
	var v_char_8: char := v_char_7;
	var v_seq_36: seq<array<int>> := m_method_12(v_seq_35, v_char_8);
	var v_char_9: char, v_int_57: int, v_multiset_2: multiset<multiset<bool>>, v_bool_22: bool := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_51]) else ((match 7.73 {
		case _ => v_char_3
	}))), (match false {
		case false => (if ((if ((v_char_4 in v_map_10)) then (v_map_10[v_char_4]) else (false))) then ((match 'j' {
			case _ => 23
		})) else ((match 'C' {
			case 'K' => 2
			case _ => -14
		})))
		case _ => v_int_45
	}), (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_56]) else (((if ((v_array_19 in v_map_11)) then (v_map_11[v_array_19]) else (multiset{multiset{true, true}, multiset({true, true, false, true})})) - (multiset({multiset({true, false}), multiset{false, true}}) * multiset{multiset{true}, multiset{}, multiset{}})))), (v_seq_34 == v_seq_36);
	var v_array_23: array<bool> := new bool[4] [false, true, false, false];
	var v_DT_1_2_17: DT_1<real> := DT_1_2(-12.79, v_array_23, 0.31);
	var v_DT_1_2_bool_bool_1: (DT_1<real>, bool, bool) := (v_DT_1_2_17, true, false);
	var v_int_int_1: (int, int) := (17, -4);
	var v_char_int_int_1: (char, (int, int)) := ('u', v_int_int_1);
	var v_int_int_2: (int, int) := (6, 11);
	var v_char_int_int_2: (char, (int, int)) := ('t', v_int_int_2);
	var v_int_int_3: (int, int) := (-25, 23);
	var v_char_int_int_3: (char, (int, int)) := ('f', v_int_int_3);
	var v_map_14: map<(DT_1<real>, bool, bool), map<(char, (int, int)), int>> := map[v_DT_1_2_bool_bool_1 := map[v_char_int_int_1 := 29, v_char_int_int_2 := 25, v_char_int_int_3 := 9]];
	var v_array_24: array<bool> := new bool[4];
	v_array_24[0] := true;
	v_array_24[1] := true;
	v_array_24[2] := true;
	v_array_24[3] := false;
	var v_DT_1_2_18: DT_1<real> := DT_1_2(-11.24, v_array_24, 22.36);
	var v_DT_1_2_bool_bool_2: (DT_1<real>, bool, bool) := (v_DT_1_2_18, false, true);
	var v_DT_1_2_bool_bool_3: (DT_1<real>, bool, bool) := v_DT_1_2_bool_bool_2;
	var v_int_int_4: (int, int) := (11, 23);
	var v_char_int_int_4: (char, (int, int)) := ('w', v_int_int_4);
	var v_int_int_5: (int, int) := (10, -28);
	var v_char_int_int_5: (char, (int, int)) := ('r', v_int_int_5);
	var v_int_int_6: (int, int) := (26, 4);
	var v_char_int_int_6: (char, (int, int)) := ('y', v_int_int_6);
	var v_int_int_7: (int, int) := (2, 5);
	var v_char_int_int_7: (char, (int, int)) := ('B', v_int_int_7);
	var v_real_bool_real_1: (real, bool, real) := (-8.12, false, -29.04);
	var v_int_real_bool_real_1: (int, (real, bool, real)) := (5, v_real_bool_real_1);
	var v_int_int_8: (int, int) := (22, 21);
	var v_char_int_int_8: (char, (int, int)) := ('R', v_int_int_8);
	var v_int_int_9: (int, int) := (28, 10);
	var v_char_int_int_9: (char, (int, int)) := ('J', v_int_int_9);
	var v_map_15: map<(int, (real, bool, real)), map<(char, (int, int)), int>> := map[v_int_real_bool_real_1 := map[v_char_int_int_8 := 16, v_char_int_int_9 := 22]];
	var v_real_bool_real_2: (real, bool, real) := (8.53, true, 28.50);
	var v_int_real_bool_real_2: (int, (real, bool, real)) := (24, v_real_bool_real_2);
	var v_int_real_bool_real_3: (int, (real, bool, real)) := v_int_real_bool_real_2;
	var v_int_int_10: (int, int) := (27, 19);
	var v_char_int_int_10: (char, (int, int)) := ('x', v_int_int_10);
	var v_int_int_11: (int, int) := (5, 1);
	var v_char_int_int_11: (char, (int, int)) := ('t', v_int_int_11);
	var v_int_int_12: (int, int) := (26, 5);
	var v_char_int_int_12: (char, (int, int)) := ('L', v_int_int_12);
	var v_int_int_13: (int, int) := (0, 29);
	var v_char_int_int_13: (char, (int, int)) := ('B', v_int_int_13);
	var v_int_int_14: (int, int) := (28, 9);
	var v_char_int_int_14: (char, (int, int)) := ('H', v_int_int_14);
	var v_map_18: map<(char, (int, int)), int> := (match 28 {
		case 0 => (if ((v_DT_1_2_bool_bool_3 in v_map_14)) then (v_map_14[v_DT_1_2_bool_bool_3]) else (map[v_char_int_int_4 := -8, v_char_int_int_5 := 26, v_char_int_int_6 := 23, v_char_int_int_7 := 29]))
		case _ => (if ((v_int_real_bool_real_3 in v_map_15)) then (v_map_15[v_int_real_bool_real_3]) else (map[v_char_int_int_10 := 1, v_char_int_int_11 := -7, v_char_int_int_12 := -1, v_char_int_int_13 := -20, v_char_int_int_14 := 24]))
	});
	var v_DT_2_1_1: DT_2 := DT_2_1;
	var v_int_int_15: (int, int) := (17, 19);
	var v_char_int_int_15: (char, (int, int)) := ('A', v_int_int_15);
	var v_DT_2_1_2: DT_2 := DT_2_1;
	var v_int_int_16: (int, int) := (29, 0);
	var v_char_int_int_16: (char, (int, int)) := ('B', v_int_int_16);
	var v_DT_2_1_3: DT_2 := DT_2_1;
	var v_map_17: map<DT_2, (char, (int, int))> := (map[v_DT_2_1_1 := v_char_int_int_15] - {v_DT_2_1_3});
	var v_DT_2_1_4: DT_2 := DT_2_1;
	var v_DT_2_1_5: DT_2 := DT_2_1;
	var v_DT_2_1_6: DT_2 := DT_2_1;
	var v_DT_2_1_7: DT_2 := DT_2_1;
	var v_DT_2_1_8: DT_2 := DT_2_1;
	var v_map_16: map<char, DT_2> := map['O' := v_DT_2_1_4, 's' := v_DT_2_1_5, 'E' := v_DT_2_1_6, 'X' := v_DT_2_1_7, 'k' := v_DT_2_1_8];
	var v_char_10: char := 'i';
	var v_DT_2_1_9: DT_2 := DT_2_1;
	var v_DT_2_1_10: DT_2 := (if ((v_char_10 in v_map_16)) then (v_map_16[v_char_10]) else (v_DT_2_1_9));
	var v_int_int_17: (int, int) := (11, 24);
	var v_char_int_int_17: (char, (int, int)) := ('K', v_int_int_17);
	var v_int_int_18: (int, int) := (25, 24);
	var v_char_int_int_18: (char, (int, int)) := ('e', v_int_int_18);
	var v_char_int_int_19: (char, (int, int)) := (if ((v_DT_2_1_10 in v_map_17)) then (v_map_17[v_DT_2_1_10]) else ((if (false) then (v_char_int_int_17) else (v_char_int_int_18))));
	var v_int_58: int := (if ((v_char_int_int_19 in v_map_18)) then (v_map_18[v_char_int_int_19]) else ((if (v_bool_18) then (v_int_51) else ((8 % 20)))));
	var v_seq_38: seq<int> := ([] + [-16]);
	var v_seq_52: seq<int> := v_seq_38;
	var v_int_int_19: (int, int) := (2, -5);
	var v_int_int_20: (int, int) := (20, 9);
	var v_int_int_21: (int, int) := (17, 12);
	var v_int_int_22: (int, int) := (4, 25);
	var v_int_int_23: (int, int) := (1, -14);
	var v_int_int_24: (int, int) := (18, 7);
	var v_int_int_25: (int, int) := (28, 22);
	var v_int_int_26: (int, int) := (25, 4);
	var v_int_int_27: (int, int) := (27, 27);
	var v_int_int_28: (int, int) := (29, -27);
	var v_int_int_29: (int, int) := (1, 1);
	var v_map_19: map<multiset<(int, int)>, int> := map[multiset{v_int_int_19, v_int_int_20, v_int_int_21, v_int_int_22} := 1, multiset{v_int_int_23} := 0, multiset({v_int_int_24, v_int_int_25, v_int_int_26}) := 10, multiset{v_int_int_27, v_int_int_28} := 15, multiset({v_int_int_29}) := 18];
	var v_multiset_3: multiset<(int, int)> := multiset({});
	var v_int_99: int := (if ((v_multiset_3 in v_map_19)) then (v_map_19[v_multiset_3]) else (24));
	var v_seq_37: seq<int> := [0, 21];
	var v_int_60: int := 11;
	var v_seq_51: seq<int> := v_seq_37;
	var v_int_95: int := v_int_60;
	var v_int_96: int := safe_index_seq(v_seq_51, v_int_95);
	v_int_60 := v_int_96;
	var v_int_100: int := (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_60]) else (23));
	var v_int_101: int, v_int_102: int := safe_subsequence(v_seq_52, v_int_99, v_int_100);
	var v_int_97: int, v_int_98: int := v_int_101, v_int_102;
	var v_seq_39: seq<int> := (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_97..v_int_98]) else (v_seq_38));
	var v_DT_3_2_1: DT_3 := DT_3_2;
	var v_int_bool_real_1: (int, bool, real) := (26, false, -3.29);
	var v_DT_3_2_int_bool_real_bool_1: (DT_3, (int, bool, real), bool) := (v_DT_3_2_1, v_int_bool_real_1, true);
	var v_map_20: map<(DT_3, (int, bool, real), bool), bool> := map[v_DT_3_2_int_bool_real_bool_1 := true];
	var v_DT_3_2_2: DT_3 := DT_3_2;
	var v_int_bool_real_2: (int, bool, real) := (23, true, -16.82);
	var v_DT_3_2_int_bool_real_bool_2: (DT_3, (int, bool, real), bool) := (v_DT_3_2_2, v_int_bool_real_2, true);
	var v_DT_3_2_int_bool_real_bool_3: (DT_3, (int, bool, real), bool) := v_DT_3_2_int_bool_real_bool_2;
	var v_array_25: array<real> := new real[4];
	v_array_25[0] := -17.64;
	v_array_25[1] := 17.27;
	v_array_25[2] := 18.78;
	v_array_25[3] := -8.34;
	var v_int_61: int := (if ((if ((v_DT_3_2_int_bool_real_bool_3 in v_map_20)) then (v_map_20[v_DT_3_2_int_bool_real_bool_3]) else (false))) then ((match 20.70 {
		case _ => 1
	})) else (v_array_25.Length));
	var v_seq_40: seq<map<real, real>> := [map[20.07 := -19.06], map[13.28 := -23.09, -15.01 := -7.25, -9.93 := -21.83, 14.02 := -18.28, 25.58 := -4.32], map[-1.21 := -18.65, -17.03 := 13.15, -19.00 := -9.86, -7.44 := 6.34, 27.05 := 11.21], map[-7.58 := -13.73, 6.92 := -1.99, -12.80 := -29.11, -28.11 := -13.13, -15.04 := -23.63]];
	var v_int_62: int := -11;
	var v_seq_53: seq<map<real, real>> := v_seq_40;
	var v_int_103: int := v_int_62;
	var v_int_104: int := safe_index_seq(v_seq_53, v_int_103);
	v_int_62 := v_int_104;
	var v_int_59: int := (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_61]) else (|(if ((|v_seq_40| > 0)) then (v_seq_40[v_int_62]) else (map[19.23 := 28.16]))|));
	while (v_int_58 < v_int_59) 
		decreases v_int_59 - v_int_58;
		invariant (v_int_58 <= v_int_59);
	{
		v_int_58 := (v_int_58 + 1);
	}
	var v_int_bool_real_3: (int, bool, real) := (26, false, -3.29);
	var v_DT_3_2_3: DT_3 := DT_3_2;
	var v_int_bool_real_4: (int, bool, real) := (23, true, -16.82);
	var v_DT_3_2_int_bool_real_bool_4: (DT_3, (int, bool, real), bool) := (v_DT_3_2_3, v_int_bool_real_4, true);
	var v_DT_3_2_4: DT_3 := DT_3_2;
	var v_int_bool_real_5: (int, bool, real) := (23, true, -16.82);
	var v_DT_3_2_int_bool_real_bool_5: (DT_3, (int, bool, real), bool) := (v_DT_3_2_4, v_int_bool_real_5, true);
	var v_DT_3_2_5: DT_3 := DT_3_2;
	var v_int_bool_real_6: (int, bool, real) := (26, false, -3.29);
	var v_DT_3_2_int_bool_real_bool_6: (DT_3, (int, bool, real), bool) := (v_DT_3_2_5, v_int_bool_real_6, true);
	var v_int_bool_real_7: (int, bool, real) := (23, true, -16.82);
	var v_int_int_30: (int, int) := (29, 0);
	var v_char_int_int_20: (char, (int, int)) := ('B', v_int_int_30);
	var v_int_int_31: (int, int) := (17, 19);
	var v_char_int_int_21: (char, (int, int)) := ('A', v_int_int_31);
	var v_int_int_32: (int, int) := (25, 24);
	var v_char_int_int_22: (char, (int, int)) := ('e', v_int_int_32);
	var v_int_int_33: (int, int) := (11, 24);
	var v_char_int_int_23: (char, (int, int)) := ('K', v_int_int_33);
	var v_int_int_34: (int, int) := (25, 24);
	var v_char_int_int_24: (char, (int, int)) := ('e', v_int_int_34);
	var v_int_int_35: (int, int) := (1, 1);
	var v_int_int_36: (int, int) := (1, -14);
	var v_int_int_37: (int, int) := (20, 9);
	var v_int_int_38: (int, int) := (4, 25);
	var v_int_int_39: (int, int) := (2, -5);
	var v_int_int_40: (int, int) := (17, 12);
	var v_int_int_41: (int, int) := (27, 27);
	var v_int_int_42: (int, int) := (29, -27);
	var v_int_int_43: (int, int) := (18, 7);
	var v_int_int_44: (int, int) := (28, 22);
	var v_int_int_45: (int, int) := (25, 4);
	var v_int_int_46: (int, int) := (26, 5);
	var v_char_int_int_25: (char, (int, int)) := ('L', v_int_int_46);
	var v_int_int_47: (int, int) := (27, 19);
	var v_char_int_int_26: (char, (int, int)) := ('x', v_int_int_47);
	var v_int_int_48: (int, int) := (28, 9);
	var v_char_int_int_27: (char, (int, int)) := ('H', v_int_int_48);
	var v_int_int_49: (int, int) := (5, 1);
	var v_char_int_int_28: (char, (int, int)) := ('t', v_int_int_49);
	var v_int_int_50: (int, int) := (0, 29);
	var v_char_int_int_29: (char, (int, int)) := ('B', v_int_int_50);
	var v_DT_2_1_11: DT_2 := DT_2_1;
	var v_DT_2_1_12: DT_2 := DT_2_1;
	var v_DT_2_1_13: DT_2 := DT_2_1;
	var v_DT_2_1_14: DT_2 := DT_2_1;
	var v_DT_2_1_15: DT_2 := DT_2_1;
	var v_DT_3_2_6: DT_3 := DT_3_2;
	var v_int_bool_real_8: (int, bool, real) := (26, false, -3.29);
	var v_DT_3_2_int_bool_real_bool_7: (DT_3, (int, bool, real), bool) := (v_DT_3_2_6, v_int_bool_real_8, true);
	var v_int_bool_real_9: (int, bool, real) := (23, true, -16.82);
	var v_int_bool_real_10: (int, bool, real) := (26, false, -3.29);
	var v_DT_1_2_26: DT_1<real> := DT_1_2(17.96, v_array_14, -26.34);
	var v_DT_1_2_27: DT_1<real> := DT_1_2(17.96, v_array_14, -26.34);
	print "v_array_14[1]", " ", v_array_14[1], " ", "v_char_int_int_18.0", " ", (v_char_int_int_18.0 == 'e'), " ", "v_char_int_int_18.1", " ", v_char_int_int_18.1, " ", "v_int_46", " ", v_int_46, " ", "v_int_45", " ", v_int_45, " ", "v_int_44", " ", v_int_44, " ", "v_array_25[3]", " ", (v_array_25[3] == -8.34), " ", "v_int_43", " ", v_int_43, " ", "v_int_49", " ", v_int_49, " ", "v_int_47", " ", v_int_47, " ", "v_int_42", " ", v_int_42, " ", "v_bool_bool_int_4", " ", v_bool_bool_int_4, " ", "v_bool_bool_int_3", " ", v_bool_bool_int_3, " ", "v_array_14[0]", " ", v_array_14[0], " ", "v_DT_2_1_10", " ", v_DT_2_1_10, " ", "v_set_1", " ", (v_set_1 == {'t', 'E', 'X'}), " ", "v_int_int_25.1", " ", v_int_int_25.1, " ", "v_int_int_25.0", " ", v_int_int_25.0, " ", "v_array_14[3]", " ", v_array_14[3], " ", "v_char_int_int_17.0", " ", (v_char_int_int_17.0 == 'K'), " ", "v_char_int_int_17.1", " ", v_char_int_int_17.1, " ", "v_array_25[1]", " ", (v_array_25[1] == 17.27), " ", "v_int_60", " ", v_int_60, " ", "v_int_62", " ", v_int_62, " ", "v_int_61", " ", v_int_61, " ", "v_array_14[2]", " ", v_array_14[2], " ", "v_int_57", " ", v_int_57, " ", "v_int_56", " ", v_int_56, " ", "v_int_55", " ", v_int_55, " ", "v_int_54", " ", v_int_54, " ", "v_array_25[2]", " ", (v_array_25[2] == 18.78), " ", "v_int_59", " ", v_int_59, " ", "v_int_58", " ", v_int_58, " ", "v_int_int_24.0", " ", v_int_int_24.0, " ", "v_int_int_24.1", " ", v_int_int_24.1, " ", "v_int_53", " ", v_int_53, " ", "v_int_52", " ", v_int_52, " ", "v_int_51", " ", v_int_51, " ", "v_int_50", " ", v_int_50, " ", "v_int_int_19.1", " ", v_int_int_19.1, " ", "v_int_int_19.0", " ", v_int_int_19.0, " ", "v_int_bool_4", " ", v_int_bool_4, " ", "v_DT_1_2_13.DT_1_2_3", " ", (v_DT_1_2_13.DT_1_2_3 == -26.34), " ", "v_int_bool_3", " ", v_int_bool_3, " ", "v_DT_1_2_13.DT_1_2_1", " ", (v_DT_1_2_13.DT_1_2_1 == 17.96), " ", "v_DT_1_2_13.DT_1_2_2", " ", (v_DT_1_2_13.DT_1_2_2 == v_array_14), " ", "v_DT_3_2_int_bool_real_bool_1.0", " ", v_DT_3_2_int_bool_real_bool_1.0, " ", "v_DT_3_2_int_bool_real_bool_1.1", " ", (v_DT_3_2_int_bool_real_bool_1.1 == v_int_bool_real_3), " ", "v_DT_3_2_int_bool_real_bool_1.2", " ", v_DT_3_2_int_bool_real_bool_1.2, " ", "v_int_int_23.1", " ", v_int_int_23.1, " ", "v_int_int_23.0", " ", v_int_int_23.0, " ", "v_array_16[1]", " ", v_array_16[1], " ", "v_int_int_18.1", " ", v_int_int_18.1, " ", "v_int_int_18.0", " ", v_int_int_18.0, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_seq_18", " ", v_seq_18, " ", "v_seq_19", " ", v_seq_19, " ", "v_bool_7", " ", v_bool_7, " ", "v_seq_14", " ", v_seq_14, " ", "v_seq_15", " ", v_seq_15, " ", "v_seq_16", " ", v_seq_16, " ", "v_seq_17", " ", v_seq_17, " ", "v_DT_3_2_int_bool_real_bool_3", " ", (v_DT_3_2_int_bool_real_bool_3 == v_DT_3_2_int_bool_real_bool_4), " ", "v_DT_3_2_int_bool_real_bool_2", " ", (v_DT_3_2_int_bool_real_bool_2 == v_DT_3_2_int_bool_real_bool_5), " ", "v_seq_13", " ", v_seq_13, " ", "v_DT_3_2_int_bool_real_bool_1", " ", (v_DT_3_2_int_bool_real_bool_1 == v_DT_3_2_int_bool_real_bool_6), " ", "v_DT_3_2_int_bool_real_bool_2.0", " ", v_DT_3_2_int_bool_real_bool_2.0, " ", "v_DT_3_2_int_bool_real_bool_2.1", " ", (v_DT_3_2_int_bool_real_bool_2.1 == v_int_bool_real_7), " ", "v_DT_3_2_int_bool_real_bool_2.2", " ", v_DT_3_2_int_bool_real_bool_2.2, " ", "v_array_16[0]", " ", v_array_16[0], " ", "v_int_bool_3.1", " ", v_int_bool_3.1, " ", "v_int_bool_3.0", " ", v_int_bool_3.0, " ", "v_DT_2_1_4", " ", v_DT_2_1_4, " ", "v_DT_2_1_3", " ", v_DT_2_1_3, " ", "v_DT_2_1_2", " ", v_DT_2_1_2, " ", "v_DT_2_1_1", " ", v_DT_2_1_1, " ", "v_char_int_int_16", " ", (v_char_int_int_16 == v_char_int_int_20), " ", "v_DT_2_1_8", " ", v_DT_2_1_8, " ", "v_char_int_int_15", " ", (v_char_int_int_15 == v_char_int_int_21), " ", "v_DT_2_1_7", " ", v_DT_2_1_7, " ", "v_DT_2_1_6", " ", v_DT_2_1_6, " ", "v_char_int_int_18", " ", (v_char_int_int_18 == v_char_int_int_22), " ", "v_DT_2_1_5", " ", v_DT_2_1_5, " ", "v_char_int_int_17", " ", (v_char_int_int_17 == v_char_int_int_23), " ", "v_char_10", " ", (v_char_10 == 'i'), " ", "v_char_int_int_19", " ", (v_char_int_int_19 == v_char_int_int_24), " ", "v_int_int_22.1", " ", v_int_int_22.1, " ", "v_DT_2_1_9", " ", v_DT_2_1_9, " ", "v_int_int_22.0", " ", v_int_int_22.0, " ", "v_int_int_19", " ", v_int_int_19, " ", "v_int_int_18", " ", v_int_int_18, " ", "v_array_16[3]", " ", v_array_16[3], " ", "v_int_int_17.0", " ", v_int_int_17.0, " ", "v_array_17[0]", " ", v_array_17[0], " ", "v_int_int_17.1", " ", v_int_int_17.1, " ", "v_map_13", " ", (v_map_13 == map[-4 := 25, 22 := -14]), " ", "v_int_bool_real_2.1", " ", v_int_bool_real_2.1, " ", "v_int_bool_real_2.2", " ", (v_int_bool_real_2.2 == -16.82), " ", "v_map_11", " ", (v_map_11 == map[v_array_16 := multiset{multiset{false, true, true}, multiset{false, false, false, true}}, v_array_17 := multiset{multiset{false}, multiset{false, false}}]), " ", "v_map_12", " ", (v_map_12 == map[false := -5, true := 27]), " ", "v_seq_36", " ", "v_seq_37", " ", v_seq_37, " ", "v_map_19", " ", (v_map_19 == map[multiset{v_int_int_35} := 18, multiset{v_int_int_36} := 0, multiset{v_int_int_37, v_int_int_38, v_int_int_39, v_int_int_40} := 1, multiset{v_int_int_41, v_int_int_42} := 15, multiset{v_int_int_43, v_int_int_44, v_int_int_45} := 10]), " ", "v_seq_38", " ", v_seq_38, " ", "v_seq_39", " ", v_seq_39, " ", "v_map_17", " ", (v_map_17 == map[]), " ", "v_seq_33", " ", (v_seq_33 == [-3.22, 21.23, -21.00]), " ", "v_map_18", " ", (v_map_18 == map[v_char_int_int_25 := -1, v_char_int_int_26 := 1, v_char_int_int_27 := 24, v_char_int_int_28 := -7, v_char_int_int_29 := -20]), " ", "v_seq_34", " ", "v_seq_35", " ", (v_seq_35 == [-11.50, 29.83, 21.25, 25.08]), " ", "v_map_16", " ", (v_map_16 == map['s' := v_DT_2_1_11, 'E' := v_DT_2_1_12, 'X' := v_DT_2_1_13, 'k' := v_DT_2_1_14, 'O' := v_DT_2_1_15]), " ", "v_int_bool_real_2.0", " ", v_int_bool_real_2.0, " ", "v_seq_30", " ", (v_seq_30 == [multiset{multiset{false, true, true, true}, multiset{false, false}}, multiset{multiset{}, multiset{false}, multiset{false, false, true, true}, multiset{true, true}}, multiset{}]), " ", "v_bool_22", " ", v_bool_22, " ", "v_seq_31", " ", (v_seq_31 == []), " ", "v_bool_20", " ", v_bool_20, " ", "v_int_int_15", " ", v_int_int_15, " ", "v_bool_21", " ", v_bool_21, " ", "v_int_int_17", " ", v_int_int_17, " ", "v_int_int_16", " ", v_int_int_16, " ", "v_array_16[2]", " ", v_array_16[2], " ", "v_bool_19", " ", v_bool_19, " ", "v_DT_3_2_2", " ", v_DT_3_2_2, " ", "v_DT_3_2_1", " ", v_DT_3_2_1, " ", "v_bool_17", " ", v_bool_17, " ", "v_bool_18", " ", v_bool_18, " ", "v_int_int_29.1", " ", v_int_int_29.1, " ", "v_bool_16", " ", v_bool_16, " ", "v_int_int_29.0", " ", v_int_int_29.0, " ", "v_multiset_3", " ", (v_multiset_3 == multiset{}), " ", "v_multiset_2", " ", (v_multiset_2 == multiset{multiset{false, true}, multiset{true, true}}), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{}), " ", "v_seq_29", " ", v_seq_29, " ", "v_map_20", " ", (v_map_20 == map[v_DT_3_2_int_bool_real_bool_7 := true]), " ", "v_seq_25", " ", v_seq_25, " ", "v_seq_26", " ", (v_seq_26 == ['u', 'e', 't']), " ", "v_seq_27", " ", (v_seq_27 == [multiset{multiset{false}, multiset{true, true}}, multiset{multiset{}, multiset{false}, multiset{false, false, true, true}, multiset{true, true}}, multiset{}]), " ", "v_seq_28", " ", (v_seq_28 == [multiset{multiset{false}, multiset{true, true}}, multiset{multiset{}, multiset{false}, multiset{false, false, true, true}, multiset{true, true}}, multiset{}]), " ", "v_seq_21", " ", (v_seq_21 == []), " ", "v_seq_22", " ", (v_seq_22 == []), " ", "v_seq_24", " ", v_seq_24, " ", "v_seq_20", " ", v_seq_20, " ", "v_bool_10", " ", v_bool_10, " ", "v_int_int_21.1", " ", v_int_int_21.1, " ", "v_int_int_21.0", " ", v_int_int_21.0, " ", "v_int_int_16.1", " ", v_int_int_16.1, " ", "v_array_17[2]", " ", v_array_17[2], " ", "v_int_int_16.0", " ", v_int_int_16.0, " ", "v_int_bool_real_1.2", " ", (v_int_bool_real_1.2 == -3.29), " ", "v_int_bool_real_1.0", " ", v_int_bool_real_1.0, " ", "v_int_bool_real_1.1", " ", v_int_bool_real_1.1, " ", "v_array_19", " ", (v_array_19 == v_array_18), " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_char_1", " ", (v_char_1 == 'J'), " ", "v_int_int_29", " ", v_int_int_29, " ", "v_map_7", " ", (v_map_7 == map['t' := multiset{20.25, -21.16, 27.93, 7.94}, 'u' := multiset{7.12, -23.15, 10.08}, 'W' := multiset{}, 'X' := multiset{-5.25}]), " ", "v_map_6", " ", (v_map_6 == map[false := false, true := true]), " ", "v_char_5", " ", (v_char_5 == 'J'), " ", "v_int_int_28.0", " ", v_int_int_28.0, " ", "v_int_bool_real_2", " ", (v_int_bool_real_2 == v_int_bool_real_9), " ", "v_int_bool_real_1", " ", (v_int_bool_real_1 == v_int_bool_real_10), " ", "v_array_17[1]", " ", v_array_17[1], " ", "v_char_7", " ", (v_char_7 == 'u'), " ", "v_char_6", " ", (v_char_6 == 'j'), " ", "v_int_int_28.1", " ", v_int_int_28.1, " ", "v_char_9", " ", (v_char_9 == 'u'), " ", "v_char_8", " ", (v_char_8 == 'u'), " ", "v_int_int_20", " ", v_int_int_20, " ", "v_int_int_22", " ", v_int_int_22, " ", "v_int_int_21", " ", v_int_int_21, " ", "v_seq_40", " ", (v_seq_40 == [map[20.07 := -19.06], map[14.02 := -18.28, 25.58 := -4.32, 13.28 := -23.09, -9.93 := -21.83, -15.01 := -7.25], map[27.05 := 11.21, -7.44 := 6.34, -1.21 := -18.65, -17.03 := 13.15, -19.00 := -9.86], map[-7.58 := -13.73, -15.04 := -23.63, 6.92 := -1.99, -12.80 := -29.11, -28.11 := -13.13]]), " ", "v_int_int_24", " ", v_int_int_24, " ", "v_int_int_23", " ", v_int_int_23, " ", "v_int_int_20.0", " ", v_int_int_20.0, " ", "v_int_int_26", " ", v_int_int_26, " ", "v_int_int_25", " ", v_int_int_25, " ", "v_int_int_28", " ", v_int_int_28, " ", "v_int_int_20.1", " ", v_int_int_20.1, " ", "v_int_int_27", " ", v_int_int_27, " ", "v_array_18[1]", " ", v_array_18[1], " ", "v_int_int_15.1", " ", v_int_int_15.1, " ", "v_char_int_int_16.0", " ", (v_char_int_int_16.0 == 'B'), " ", "v_char_int_int_16.1", " ", v_char_int_int_16.1, " ", "v_int_int_15.0", " ", v_int_int_15.0, " ", "v_array_17[4]", " ", v_array_17[4], " ", "v_array_17[3]", " ", v_array_17[3], " ", "v_int_int_27.1", " ", v_int_int_27.1, " ", "v_int_int_27.0", " ", v_int_int_27.0, " ", "v_array_18[0]", " ", v_array_18[0], " ", "v_array_25[0]", " ", (v_array_25[0] == -17.64), " ", "v_DT_1_2_13", " ", (v_DT_1_2_13 == v_DT_1_2_26), " ", "v_DT_1_2_16", " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_DT_1_2_15", " ", "v_DT_1_2_14", " ", (v_DT_1_2_14 == v_DT_1_2_27), " ", "v_char_int_int_15.0", " ", (v_char_int_int_15.0 == 'A'), " ", "v_char_int_int_15.1", " ", v_char_int_int_15.1, " ", "v_array_18[2]", " ", v_array_18[2], " ", "v_int_int_26.1", " ", v_int_int_26.1, " ", "v_int_int_26.0", " ", v_int_int_26.0, "\n";
}
