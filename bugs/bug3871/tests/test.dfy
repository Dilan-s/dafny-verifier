datatype DT_1 = DT_1_1 | DT_1_2(DT_1_2_1: int, DT_1_2_2: int, DT_1_2_3: int)
datatype DT_2<T_1, T_2> = DT_2_1 | DT_2_3
datatype DT_3<T_3> = DT_3_1
datatype DT_4 = DT_4_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: int, p_m_method_3_3: int, p_m_method_3_4: int) returns (ret_1: int, ret_2: int)
	requires ((p_m_method_3_1 == 20) && (p_m_method_3_3 == 0) && (p_m_method_3_2 == 0) && (p_m_method_3_4 == 28));
	ensures (((p_m_method_3_1 == 20) && (p_m_method_3_3 == 0) && (p_m_method_3_2 == 0) && (p_m_method_3_4 == 28)) ==> ((ret_1 == 5) && (ret_2 == -21)));
{
	var v_map_2: map<int, int> := map[-22 := 1, 26 := -17, 27 := 29, 17 := 18, 29 := 18];
	var v_int_25: int := 29;
	var v_int_26: int := (if ((v_int_25 in v_map_2)) then (v_map_2[v_int_25]) else (17));
	var v_int_27: int := p_m_method_3_1;
	var v_int_28: int := (-21.00).Floor;
	var v_int_29: int := (if (false) then (-27) else (6));
	var v_bool_5: bool := m_method_2(v_int_26, v_int_27, v_int_28, v_int_29);
	if v_bool_5 {
		var v_map_3: map<int, int> := (match 17 {
			case 4 => map[16 := 5, 15 := 9, 14 := 25]
			case _ => map[23 := 26, 17 := 9]
		});
		var v_int_30: int := v_int_25;
		var v_array_7: array<multiset<bool>> := new multiset<bool>[5] [multiset{true, false}, multiset{true, true, false}, multiset{false, true}, multiset{}, multiset{true, false}];
		print "v_array_7[1]", " ", (v_array_7[1] == multiset{false, true, true}), " ", "v_array_7[2]", " ", (v_array_7[2] == multiset{false, true}), " ", "v_array_7[3]", " ", (v_array_7[3] == multiset{}), " ", "v_array_7[4]", " ", (v_array_7[4] == multiset{false, true}), " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_int_30", " ", v_int_30, " ", "v_map_3", " ", (v_map_3 == map[17 := 9, 23 := 26]), " ", "v_array_7[0]", " ", (v_array_7[0] == multiset{false, true}), " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_int_25", " ", v_int_25, " ", "v_int_29", " ", v_int_29, " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "v_bool_5", " ", v_bool_5, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", p_m_method_3_4, " ", "p_m_method_3_3", " ", p_m_method_3_3, " ", "v_map_2", " ", (v_map_2 == map[17 := 18, -22 := 1, 26 := -17, 27 := 29, 29 := 18]), "\n";
		return (if ((v_int_30 in v_map_3)) then (v_map_3[v_int_30]) else (v_array_7.Length)), v_int_28;
	} else {
		
	}
	if (match 12 {
		case _ => ({-2, 11, 6} !! {26, 0, 10})
	}) {
		var v_map_4: map<multiset<set<bool>>, int> := (map[multiset{{false, false, false, false}, {}, {false, false}} := 16, multiset{{false, true, false, true}} := 23, multiset({{true, true, false}, {true, true, false}}) := 13, multiset({{}, {false}, {}, {true, true, false}}) := 28] + map[multiset{{true, false}} := 23, multiset{{false, false}, {}, {}} := 6, multiset({{false, false}, {}, {true, false, true, false}, {false}}) := 21, multiset({{false, false, true}, {false, false}}) := 29]);
		var v_multiset_1: multiset<set<bool>> := (multiset{{true}, {false, true, false, false}} - multiset({{true}, {false, false, true}, {false, true, false, false}}));
		var v_array_8: array<int> := new int[3] [-14, 0, 4];
		var v_array_9: array<int> := new int[3] [0, 5, 22];
		var v_array_10: array<int> := new int[3] [23, 1, 17];
		var v_array_11: array<int> := new int[3] [9, -22, 2];
		var v_seq_5: seq<array<int>> := [v_array_8, v_array_9, v_array_10, v_array_11];
		var v_int_31: int := 24;
		var v_array_12: array<int> := new int[4] [11, 12, 14, 26];
		return (if ((v_multiset_1 in v_map_4)) then (v_map_4[v_multiset_1]) else (|multiset{true, true, false, true}|)), (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_31]) else (v_array_12)).Length;
	}
	var v_seq_6: seq<real> := [-7.86];
	var v_int_32: int := 29;
	return ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_32]) else (2.36))).Floor, (match 4 {
		case _ => (-28 / 10)
	});
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: int, p_m_method_2_3: int, p_m_method_2_4: int) returns (ret_1: bool)
	requires ((p_m_method_2_2 == 20) && (p_m_method_2_1 == 18) && (p_m_method_2_4 == 6) && (p_m_method_2_3 == -21)) || ((p_m_method_2_2 == 25) && (p_m_method_2_1 == 5) && (p_m_method_2_4 == 20) && (p_m_method_2_3 == 8));
	ensures (((p_m_method_2_2 == 25) && (p_m_method_2_1 == 5) && (p_m_method_2_4 == 20) && (p_m_method_2_3 == 8)) ==> ((ret_1 == true))) && (((p_m_method_2_2 == 20) && (p_m_method_2_1 == 18) && (p_m_method_2_4 == 6) && (p_m_method_2_3 == -21)) ==> ((ret_1 == true)));
{
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", p_m_method_2_2, " ", "p_m_method_2_4", " ", p_m_method_2_4, "\n";
	return true;
}

method m_method_1(p_m_method_1_1: int, p_m_method_1_2: bool, p_m_method_1_3: bool, p_m_method_1_4: array<real>) returns (ret_1: bool)
	requires ((p_m_method_1_1 == 20) && (p_m_method_1_3 == true) && (p_m_method_1_2 == true) && p_m_method_1_4.Length == 4 && (28.08 < p_m_method_1_4[0] < 28.28) && (9.39 < p_m_method_1_4[1] < 9.59) && (2.25 < p_m_method_1_4[2] < 2.45) && (-14.28 < p_m_method_1_4[3] < -14.08));
	ensures (((p_m_method_1_1 == 20) && (p_m_method_1_3 == true) && (p_m_method_1_2 == true) && p_m_method_1_4.Length == 4 && (28.08 < p_m_method_1_4[0] < 28.28) && (9.39 < p_m_method_1_4[1] < 9.59) && (2.25 < p_m_method_1_4[2] < 2.45) && (-14.28 < p_m_method_1_4[3] < -14.08)) ==> ((ret_1 == false)));
{
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_DT_1_1_3: DT_1 := DT_1_1;
	var v_DT_1_1_4: DT_1 := DT_1_1;
	var v_DT_1_1_5: DT_1 := DT_1_1;
	var v_DT_1_1_6: DT_1 := DT_1_1;
	var v_DT_1_1_7: DT_1 := DT_1_1;
	var v_DT_1_1_8: DT_1 := DT_1_1;
	var v_seq_3: seq<bool> := [true, false];
	var v_int_14: int := 24;
	var v_seq_98: seq<bool> := v_seq_3;
	var v_int_171: int := v_int_14;
	var v_int_172: int := safe_index_seq(v_seq_98, v_int_171);
	v_int_14 := v_int_172;
	var v_int_15: int := 5;
	var v_int_16: int := 25;
	var v_int_17: int := 8;
	var v_int_18: int := 20;
	var v_bool_1: bool := m_method_2(v_int_15, v_int_16, v_int_17, v_int_18);
	var v_array_1: array<int> := new int[3] [15, 19, 5];
	var v_array_2: array<int> := new int[3] [28, 16, 26];
	var v_bool_2: bool, v_char_1: char, v_bool_3: bool, v_set_1: set<array<int>> := ((if (true) then ({v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3}) else ({v_DT_1_1_4, v_DT_1_1_5, v_DT_1_1_6})) < ({v_DT_1_1_7, v_DT_1_1_8} * {})), 'p', (if ((false <== false)) then ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_14]) else (true))) else (v_bool_1)), ((if (false) then (map[v_array_1 := 0]) else (map[v_array_2 := 10]))).Keys;
	if v_bool_2 {
		var v_array_3: array<int> := new int[4] [5, 27, 24, 11];
		var v_array_4: array<int> := new int[3] [27, -18, 6];
		var v_array_5: array<int> := new int[5] [16, 22, 23, 12, -18];
		var v_seq_4: seq<array<int>> := [v_array_3, v_array_4, v_array_5];
		var v_int_19: int := 27;
		var v_array_6: array<int> := new int[5] [23, 0, 9, 9, 2];
		v_array_4[0], v_array_5[4] := v_array_2[1], (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_19]) else (v_array_6)).Length;
		if v_bool_3 {
			var v_map_1: map<int, int> := map[6 := 19, 27 := -2];
			var v_int_20: int := 9;
			var v_int_21: int := (if ((v_int_20 in v_map_1)) then (v_map_1[v_int_20]) else (-21));
			var v_int_22: int := v_array_4[1];
			var v_int_23: int := v_array_5[0];
			var v_int_24: int := v_array_5[0];
			var v_bool_4: bool := m_method_2(v_int_21, v_int_22, v_int_23, v_int_24);
			return v_bool_4;
		} else {
			return p_m_method_1_2;
		}
	}
	var v_seq_7: seq<bool> := [false, true, true, false];
	var v_int_33: int := 4;
	var v_seq_99: seq<bool> := v_seq_7;
	var v_int_173: int := v_int_33;
	var v_int_174: int := safe_index_seq(v_seq_99, v_int_173);
	v_int_33 := v_int_174;
	var v_seq_8: seq<char> := ['Z', 'w', 'r'];
	var v_int_34: int := 23;
	var v_int_35: int := safe_index_seq(v_seq_8, v_int_34);
	var v_int_37: int := (if ((if ((|v_seq_7| > 0)) then (v_seq_7[v_int_33]) else (false))) then (v_int_35) else (v_int_18));
	var v_int_38: int := v_int_14;
	var v_int_39: int := v_int_33;
	var v_seq_9: seq<int> := [28, 12, -4];
	var v_int_36: int := 14;
	var v_seq_100: seq<int> := v_seq_9;
	var v_int_175: int := v_int_36;
	var v_int_176: int := safe_index_seq(v_seq_100, v_int_175);
	v_int_36 := v_int_176;
	var v_int_40: int := (if ((false != true)) then ((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_36]) else (25))) else (v_array_2[1]));
	var v_int_41: int, v_int_42: int := m_method_3(v_int_37, v_int_38, v_int_39, v_int_40);
	v_int_39, v_int_14 := v_int_41, v_int_42;
	if v_bool_1 {
		match p_m_method_1_4[0] {
			case 3.11 => {
				
			}
				case _ => {
				var v_map_5: map<bool, bool> := map[false := false, true := false];
				var v_bool_6: bool := true;
				print "v_map_5", " ", (v_map_5 == map[false := false, true := false]), " ", "v_bool_6", " ", v_bool_6, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_3", " ", v_bool_3, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_18", " ", v_int_18, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "p_m_method_1_4[0]", " ", (p_m_method_1_4[0] == 28.18), " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "p_m_method_1_4[2]", " ", (p_m_method_1_4[2] == 2.35), " ", "v_array_1[0]", " ", v_array_1[0], " ", "p_m_method_1_4", " ", "v_int_42", " ", v_int_42, " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_char_1", " ", (v_char_1 == 'p'), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", (v_seq_8 == ['Z', 'w', 'r']), " ", "v_int_35", " ", v_int_35, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_17", " ", v_int_17, " ", "v_set_1", " ", (v_set_1 == {v_array_2}), " ", "v_int_39", " ", v_int_39, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_16", " ", v_int_16, " ", "v_int_38", " ", v_int_38, " ", "v_int_15", " ", v_int_15, " ", "v_int_37", " ", v_int_37, " ", "v_int_14", " ", v_int_14, " ", "v_int_36", " ", v_int_36, " ", "p_m_method_1_4[1]", " ", (p_m_method_1_4[1] == 9.49), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
				return (if ((if ((v_bool_6 in v_map_5)) then (v_map_5[v_bool_6]) else (false))) then ((false && false)) else (v_bool_2));
			}
			
		}
		
		var v_int_44: int, v_int_45: int := v_int_37, (match -12.09 {
			case _ => (match false {
				case _ => -7
			})
		});
		for v_int_43 := v_int_44 to v_int_45 
			invariant (v_int_45 - v_int_43 >= 0)
		{
			
		}
		assert true;
		expect true;
		var v_map_6: map<bool, int> := (map[true := 17, true := 28, true := 14, false := 2, true := 6] - {true, true, false, true});
		var v_bool_7: bool := (multiset{} !! multiset{false});
		var v_int_49: int, v_int_50: int := (match false {
			case _ => (match false {
				case _ => 4
			})
		}), (if ((v_bool_7 in v_map_6)) then (v_map_6[v_bool_7]) else (v_array_1[0]));
		for v_int_46 := v_int_49 to v_int_50 
			invariant (v_int_50 - v_int_46 >= 0)
		{
			var v_map_7: map<bool, seq<bool>> := map[true := [true, false, false], false := [false], false := [true, false], true := [true, false], true := [false, true]];
			var v_bool_8: bool := true;
			var v_seq_11: seq<bool> := (if ((v_bool_8 in v_map_7)) then (v_map_7[v_bool_8]) else ([false, true]));
			var v_seq_10: seq<int> := [4, 26, 16];
			var v_int_47: int := 19;
			var v_int_48: int := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_47]) else (0));
			return (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_48]) else ((match false {
				case _ => false
			})));
		}
		var v_seq_12: seq<bool> := (if (true) then ([false, false]) else ([]));
		var v_map_8: map<bool, int> := map[true := 28, true := -24];
		var v_bool_9: bool := false;
		var v_int_51: int := (if ((v_bool_9 in v_map_8)) then (v_map_8[v_bool_9]) else (16));
		var v_map_10: map<bool, bool> := (if (false) then (map[true := true, true := true, false := false, true := true]) else (map[true := true, true := true]));
		var v_seq_13: seq<bool> := [false, false, true];
		var v_int_52: int := -20;
		var v_bool_11: bool := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_52]) else (false));
		var v_map_9: map<bool, bool> := map[false := false, true := true, true := false, true := false];
		var v_bool_10: bool := false;
		v_bool_3, v_bool_9, v_bool_7, v_bool_11 := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_51]) else (('Y' != 'V'))), (!(false) && (true <==> false)), (v_bool_7 && (false && false)), (if ((v_bool_11 in v_map_10)) then (v_map_10[v_bool_11]) else ((if ((v_bool_10 in v_map_9)) then (v_map_9[v_bool_10]) else (false))));
	} else {
		var v_array_13: array<bool> := new bool[3] [false, true, false];
		var v_map_11: map<bool, bool> := map[false := true];
		var v_bool_12: bool := false;
		var v_seq_14: seq<map<bool, bool>> := [map[true := true, true := true, true := false], map[true := true]];
		var v_int_53: int := 6;
		var v_map_12: map<bool, bool> := (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_53]) else (map[true := true, false := false, false := false, false := false, false := true]));
		var v_bool_13: bool := (true !in map[false := false, true := false, false := true, true := false, false := false]);
		v_bool_1, v_array_13[0], v_bool_2, v_bool_13 := ((if (true) then (22) else (26)) >= v_array_13.Length), (match false {
			case _ => (if ((v_bool_12 in v_map_11)) then (v_map_11[v_bool_12]) else (false))
		}), (if ((v_bool_13 in v_map_12)) then (v_map_12[v_bool_13]) else ((true in map[true := false, true := true, true := false, true := false, false := false]))), v_array_13[2];
	}
	var v_seq_15: seq<int> := [7, 15];
	var v_int_55: int := 16;
	var v_int_56: int, v_int_57: int := v_int_18, (match false {
		case _ => (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_55]) else (20))
	});
	for v_int_54 := v_int_56 to v_int_57 
		invariant (v_int_57 - v_int_54 >= 0)
	{
		var v_map_13: map<bool, bool> := map[false := false, false := false, false := false];
		var v_bool_14: bool := true;
		return (if ((false <== false)) then ((if (false) then (true) else (true))) else ((if ((v_bool_14 in v_map_13)) then (v_map_13[v_bool_14]) else (false))));
	}
	var v_map_14: map<bool, map<bool, bool>> := map[false := map[true := false], false := map[false := false, false := false, false := false], true := map[false := false], true := map[false := false, false := true, true := true, true := true]];
	var v_bool_15: bool := true;
	var v_int_58: int := |(if ((v_bool_15 in v_map_14)) then (v_map_14[v_bool_15]) else (map[false := true, false := true]))|;
	var v_int_59: int := v_int_16;
	while (v_int_58 < v_int_59) 
		decreases v_int_59 - v_int_58;
		invariant (v_int_58 <= v_int_59);
	{
		v_int_58 := (v_int_58 + 1);
		assert true;
		expect true;
		break;
	}
	return v_bool_15;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_int_8: int := (if (true) then (22) else (12));
	var v_int_9: int := (if (false) then (24) else (17));
	var v_int_10: int := safe_modulus(v_int_8, v_int_9);
	var v_int_11: int := v_int_10;
	var v_int_12: int := v_int_10;
	var v_int_13: int := safe_modulus(v_int_11, v_int_12);
	var v_int_74: int, v_int_75: int := v_int_13, (match 'z' {
		case 'L' => v_int_13
		case _ => 15
	});
	for v_int_7 := v_int_74 to v_int_75 
		invariant (v_int_75 - v_int_7 >= 0)
	{
		var v_map_15: map<bool, int> := map[false := 28];
		var v_bool_16: bool := true;
		var v_int_65: int := (if ((if (false) then (false) else (true))) then ((if ((v_bool_16 in v_map_15)) then (v_map_15[v_bool_16]) else (20))) else ((13 - 10)));
		var v_map_16: map<bool, bool> := map[true := true, false := true][false := true];
		var v_seq_16: seq<bool> := [false, false];
		var v_int_60: int := 15;
		var v_seq_95: seq<bool> := v_seq_16;
		var v_int_165: int := v_int_60;
		var v_int_166: int := safe_index_seq(v_seq_95, v_int_165);
		v_int_60 := v_int_166;
		var v_bool_17: bool := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_60]) else (false));
		var v_bool_18: bool := (if ((v_bool_17 in v_map_16)) then (v_map_16[v_bool_17]) else ((multiset({true}) == multiset{})));
		var v_seq_17: seq<int> := [-5];
		var v_int_61: int := 28;
		var v_seq_96: seq<int> := v_seq_17;
		var v_int_167: int := v_int_61;
		var v_int_168: int := safe_index_seq(v_seq_96, v_int_167);
		v_int_61 := v_int_168;
		var v_seq_18: seq<int> := [18, 6, 18];
		var v_int_62: int := 2;
		var v_bool_19: bool := ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_61]) else (16)) != (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_62]) else (-11)));
		var v_array_14: array<real> := new real[4] [-20.66, 18.50, -19.89, -18.67];
		var v_array_15: array<real> := new real[4] [-26.19, -26.61, -4.43, 20.62];
		var v_array_16: array<real> := new real[3] [-12.91, 15.81, -28.13];
		var v_seq_19: seq<array<real>> := [v_array_14, v_array_15, v_array_16];
		var v_int_63: int := 0;
		var v_array_17: array<real> := new real[5] [-9.11, -1.91, 6.10, 3.59, -25.60];
		var v_array_18: array<real> := new real[4] [28.18, 9.49, 2.35, -14.18];
		var v_array_19: array<real> := new real[5] [-17.93, -29.03, -21.51, -29.48, 22.13];
		var v_array_20: array<real> := new real[5] [-3.10, -13.25, 21.52, 14.97, 7.51];
		var v_array_21: array<real> := new real[3];
		v_array_21[0] := 8.50;
		v_array_21[1] := 9.37;
		v_array_21[2] := 6.65;
		var v_seq_20: seq<array<real>> := [v_array_18, v_array_19, v_array_20, v_array_21];
		var v_int_64: int := 4;
		var v_seq_97: seq<array<real>> := v_seq_20;
		var v_int_169: int := v_int_64;
		var v_int_170: int := safe_index_seq(v_seq_97, v_int_169);
		v_int_64 := v_int_170;
		var v_array_22: array<real> := new real[4] [5.09, -4.33, 14.65, -8.46];
		var v_array_23: array<real> := new real[5] [23.18, -13.41, 27.28, -1.67, -17.26];
		var v_array_24: array<real> := new real[4] [3.09, 18.34, 10.62, -20.01];
		var v_array_25: array<real> := (match true {
			case false => (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_63]) else (v_array_17))
			case true => (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_64]) else (v_array_22))
			case _ => (match false {
				case _ => v_array_24
			})
		});
		var v_bool_20: bool := m_method_1(v_int_65, v_bool_18, v_bool_19, v_array_25);
		if v_bool_20 {
			var v_seq_21: seq<map<bool, int>> := [map[false := -20, true := -8, true := -7], map[false := 20, true := 4, true := -7, false := 25], map[false := 11, false := 9, true := 3, true := 18], map[true := 15, false := 13, true := -9, false := 21]];
			var v_int_66: int := 27;
			var v_map_18: map<bool, int> := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_66]) else (map[false := 5]));
			var v_bool_22: bool := (true !in {false, true});
			var v_map_17: map<bool, int> := map[false := 11, false := 12, true := 10, false := 22, false := 0];
			var v_bool_21: bool := true;
			match (((24 + 26) - v_int_62) * (if ((v_bool_22 in v_map_18)) then (v_map_18[v_bool_22]) else ((if ((v_bool_21 in v_map_17)) then (v_map_17[v_bool_21]) else (17))))) {
				case _ => {
					var v_int_67: int := 9;
					var v_int_68: int := 26;
					var v_int_69: int := safe_modulus(v_int_67, v_int_68);
					var v_map_19: map<int, int> := map[14 := 17, 21 := 8];
					var v_int_70: int := 0;
					var v_map_21: map<int, int> := map[27 := 17, 27 := 17, 6 := 16][11 := 6][v_int_69 := (if ((v_int_70 in v_map_19)) then (v_map_19[v_int_70]) else (18))];
					var v_map_20: map<int, int> := map[27 := 6, 18 := 3, 24 := 18][9 := 19];
					var v_int_72: int := (match 9 {
						case _ => 22
					});
					var v_seq_22: seq<int> := [];
					var v_int_71: int := 3;
					var v_int_73: int := (if ((v_int_72 in v_map_20)) then (v_map_20[v_int_72]) else ((if ((|v_seq_22| > 0)) then (v_seq_22[v_int_71]) else (20))));
					match (if ((v_int_73 in v_map_21)) then (v_map_21[v_int_73]) else (v_int_62)) {
						case _ => {
							return ;
						}
						
					}
					
				}
				
			}
			
		} else {
			print "v_bool_19", " ", v_bool_19, " ", "v_bool_17", " ", v_bool_17, " ", "v_bool_18", " ", v_bool_18, " ", "v_bool_16", " ", v_bool_16, " ", "v_int_7", " ", v_int_7, " ", "v_seq_18", " ", v_seq_18, " ", "v_seq_16", " ", v_seq_16, " ", "v_seq_17", " ", v_seq_17, " ", "v_int_65", " ", v_int_65, " ", "v_map_15", " ", (v_map_15 == map[false := 28]), " ", "v_map_16", " ", (v_map_16 == map[false := true, true := true]), " ", "v_int_60", " ", v_int_60, " ", "v_bool_20", " ", v_bool_20, " ", "v_array_25", " ", "v_int_62", " ", v_int_62, " ", "v_int_61", " ", v_int_61, " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, "\n";
			return ;
		}
	}
	assert true;
	expect true;
	var v_map_22: map<int, bool> := map[-10 := true, 2 := true, 20 := false, 13 := false];
	var v_int_76: int := 1;
	if !(((if (true) then (true) else (false)) <==> (if ((v_int_76 in v_map_22)) then (v_map_22[v_int_76]) else (true)))) {
		assert true;
		expect true;
		var v_seq_23: seq<map<int, int>> := [];
		var v_int_77: int := 17;
		var v_map_23: map<int, int> := (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_77]) else (map[19 := 10, 16 := 21, 2 := 3, 12 := 18]));
		var v_int_79: int := |[21, -15]|;
		var v_seq_24: seq<int> := [5, 24, 14];
		var v_int_78: int := 17;
		var v_seq_25: seq<int> := [23, 20, 19, 14];
		var v_seq_27: seq<int> := (match 27 {
			case _ => (if ((|v_seq_25| > 0)) then (v_seq_25[-21..9]) else (v_seq_25))
		});
		var v_seq_26: seq<bool> := [true];
		var v_int_80: int := 15;
		var v_int_81: int := (if ((if ((|v_seq_26| > 0)) then (v_seq_26[v_int_80]) else (true))) then ((match 18 {
			case _ => 21
		})) else ((6 + 28)));
		var v_map_25: map<int, bool> := v_map_22;
		var v_map_24: map<int, int> := map[1 := 29];
		var v_int_82: int := 19;
		var v_int_83: int := (if ((v_int_82 in v_map_24)) then (v_map_24[v_int_82]) else (23));
		var v_seq_28: seq<int> := [2, 21];
		var v_seq_29: seq<int> := v_seq_28;
		var v_int_84: int := 0;
		var v_int_85: int := safe_index_seq(v_seq_29, v_int_84);
		var v_int_86: int := v_int_85;
		var v_seq_30: seq<int> := (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_86 := 25]) else (v_seq_28));
		var v_map_26: map<int, int> := map[0 := 15, 14 := 9, 22 := 12, 25 := 22];
		var v_int_87: int := 29;
		var v_int_88: int := (if ((v_int_87 in v_map_26)) then (v_map_26[v_int_87]) else (17));
		v_int_13, v_int_12, v_int_11, v_int_86, v_int_81 := (match -3 {
			case _ => (if ((v_int_79 in v_map_23)) then (v_map_23[v_int_79]) else ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_78]) else (6))))
		}), v_int_11, (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_81]) else (((if (true) then (-23.39) else (26.17))).Floor)), v_int_76, (if ((if ((v_int_83 in v_map_25)) then (v_map_25[v_int_83]) else ((27 !in [26, 10])))) then (v_int_76) else ((if ((|v_seq_30| > 0)) then (v_seq_30[v_int_88]) else (v_int_81))));
		var v_map_27: map<int, bool> := map[25 := false, 0 := true, 1 := true, 16 := true][17 := true];
		var v_int_90: int := v_int_80;
		var v_seq_31: seq<bool> := [true];
		var v_int_89: int := 16;
		var v_seq_32: seq<bool> := [];
		var v_seq_33: seq<bool> := v_seq_32;
		var v_int_91: int := -25;
		var v_int_92: int := safe_index_seq(v_seq_33, v_int_91);
		var v_int_93: int := v_int_92;
		var v_seq_34: seq<bool> := (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_93 := true]) else (v_seq_32));
		var v_int_94: int := (-16 * -2);
		var v_seq_35: seq<int> := [7, 4];
		var v_int_95: int := 28;
		if (if ((if ((v_int_90 in v_map_27)) then (v_map_27[v_int_90]) else ((if ((|v_seq_31| > 0)) then (v_seq_31[v_int_89]) else (true))))) then ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_94]) else (({29, 1, 3, 3} <= {5, 27})))) else (((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_95]) else (6)) > (16 + 11)))) {
			assert true;
			expect true;
			var v_seq_36: seq<int> := [25];
			var v_int_96: int := 10;
			var v_int_int_int_1: (int, int, int) := (16, 17, 7);
			var v_int_int_int_2: (int, int, int) := (12, -1, -22);
			var v_int_int_int_3: (int, int, int) := (21, 8, 3);
			var v_int_int_int_4: (int, int, int) := (8, 16, 1);
			var v_int_int_int_5: (int, int, int) := (12, 28, -21);
			var v_int_int_int_6: (int, int, int) := (14, 17, 26);
			var v_map_29: map<(int, int, int), int> := map[v_int_int_int_1 := 15, v_int_int_int_2 := 11, v_int_int_int_3 := 27, v_int_int_int_4 := 19, v_int_int_int_5 := 4][v_int_int_int_6 := 7];
			var v_int_int_int_7: (int, int, int) := (10, 0, 5);
			var v_int_int_int_8: (int, int, int) := (11, 3, 9);
			var v_int_int_int_9: (int, int, int) := (if (true) then (v_int_int_int_7) else (v_int_int_int_8));
			var v_map_28: map<int, int> := map[11 := 7, 5 := 21, 9 := 1, 6 := -24];
			var v_int_97: int := 1;
			var v_seq_37: seq<int> := [27, 9, -3];
			var v_seq_38: seq<int> := (if ((|v_seq_37| > 0)) then (v_seq_37[11..24]) else (v_seq_37));
			var v_int_98: int := (if (false) then (-10) else (26));
			var v_seq_39: seq<int> := ([] + [26]);
			var v_seq_40: seq<int> := (if ((|v_seq_39| > 0)) then (v_seq_39[|{8, 1, 9, -26}|..v_int_int_int_1.2]) else (v_seq_39));
			var v_int_99: int := v_int_8;
			var v_seq_41: seq<seq<bool>> := [[false], [], [true], [false, false]];
			var v_int_100: int := 22;
			var v_seq_42: seq<bool> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_100]) else ([true]));
			var v_int_101: int := (if (false) then (14) else (2));
			var v_int_int_int_10: (int, int, int) := (28, 1, 0);
			var v_int_int_int_11: (int, int, int) := (-29, 28, 11);
			var v_int_int_int_12: (int, int, int) := (8, 7, 19);
			var v_int_int_int_13: (int, int, int) := (16, -28, 11);
			var v_int_int_int_14: (int, int, int) := (24, 17, 23);
			var v_map_30: map<(int, int, int), bool> := map[v_int_int_int_10 := false, v_int_int_int_11 := false, v_int_int_int_12 := false, v_int_int_int_13 := false, v_int_int_int_14 := false];
			var v_int_int_int_15: (int, int, int) := (-9, 29, 19);
			var v_int_int_int_16: (int, int, int) := v_int_int_int_15;
			var v_seq_43: seq<int> := [28, 0];
			var v_int_102: int := 18;
			var v_map_31: map<int, int> := map[16 := 0, 22 := 20];
			var v_int_103: int := 21;
			var v_seq_44: seq<int> := [26, 25, -1, 21];
			var v_seq_45: seq<int> := (if ((|v_seq_44| > 0)) then (v_seq_44[20..19]) else (v_seq_44));
			var v_map_32: map<int, int> := map[0 := 19];
			var v_int_104: int := 5;
			var v_int_105: int := (if ((v_int_104 in v_map_32)) then (v_map_32[v_int_104]) else (24));
			var v_seq_46: seq<int> := [27, 17];
			var v_int_106: int := 25;
			v_int_106, v_int_104, v_int_88, v_int_101, v_int_12 := ((if ((match -6 {
				case _ => false
			})) then ((if ((|v_seq_36| > 0)) then (v_seq_36[v_int_96]) else (25))) else ((6 / 2))) - v_int_96), v_int_13, ((if ((v_int_int_int_9 in v_map_29)) then (v_map_29[v_int_int_int_9]) else ((if ((v_int_97 in v_map_28)) then (v_map_28[v_int_97]) else (17)))) % (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_98]) else (v_int_int_int_6.0))), (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_99]) else (v_int_int_int_8.0)), (if ((if ((|v_seq_42| > 0)) then (v_seq_42[v_int_101]) else ((if ((v_int_int_int_16 in v_map_30)) then (v_map_30[v_int_int_int_16]) else (true))))) then ((match 19 {
				case _ => (if ((v_int_103 in v_map_31)) then (v_map_31[v_int_103]) else (1))
			})) else ((if ((|v_seq_45| > 0)) then (v_seq_45[v_int_105]) else ((if ((|v_seq_46| > 0)) then (v_seq_46[v_int_106]) else (1))))));
		}
	} else {
		var v_map_33: map<int, bool> := map[29 := false, 25 := true, 26 := false];
		var v_int_107: int := 10;
		var v_map_34: map<int, bool> := map[16 := false, 21 := true, -23 := true];
		var v_int_108: int := 6;
		var v_map_35: map<int, bool> := map[27 := true][0 := true];
		var v_int_109: int := (28 + 3);
		var v_seq_47: seq<bool> := [];
		var v_int_110: int := -2;
		var v_map_36: map<int, bool> := map[12 := true, 26 := false, -23 := true, 10 := false];
		var v_int_111: int := 16;
		if (if ((match -9 {
			case _ => (if ((v_int_108 in v_map_34)) then (v_map_34[v_int_108]) else (false))
		})) then ((if ((v_int_109 in v_map_35)) then (v_map_35[v_int_109]) else ((match -25 {
			case _ => false
		})))) else ((if ((match -4 {
			case _ => true
		})) then ((if ((|v_seq_47| > 0)) then (v_seq_47[v_int_110]) else (false))) else ((if ((v_int_111 in v_map_36)) then (v_map_36[v_int_111]) else (true)))))) {
			var v_map_38: map<multiset<set<real>>, bool> := (match true {
				case _ => map[multiset({}) := false, multiset{{}, {-21.63, -18.27, -5.53, -19.46}} := false]
			});
			var v_map_37: map<multiset<map<real, bool>>, multiset<set<real>>> := map[multiset{map[-16.71 := true, 26.38 := true, -1.78 := true, 26.76 := false], map[29.44 := false, 7.49 := false, 17.40 := false, -26.03 := true, -6.37 := false], map[-1.89 := true, 20.02 := false], map[10.86 := true, -24.94 := false, 2.72 := true, 12.93 := false]} := multiset{{}}, multiset{map[-6.14 := false], map[-7.92 := true, -14.79 := false, -11.69 := true], map[-22.89 := true], map[0.94 := true, -26.52 := true, -0.18 := false, -26.13 := false, -3.17 := false]} := multiset({{-17.16, -28.64}, {}, {}, {13.48}}), multiset{map[6.63 := true, 14.83 := false, -9.75 := false, 24.37 := false], map[14.19 := false, 23.41 := true]} := multiset{{-14.01}, {-21.95, -1.10, 29.20}, {-2.61, 15.29, -29.83, 22.23}}];
			var v_multiset_2: multiset<map<real, bool>> := multiset{map[0.31 := true, 20.39 := true], map[15.45 := false, -27.09 := true], map[20.91 := true], map[-17.04 := true, -5.79 := true, -9.09 := false, -1.84 := true, -21.86 := false]};
			var v_multiset_3: multiset<set<real>> := (if ((v_multiset_2 in v_map_37)) then (v_map_37[v_multiset_2]) else (multiset{{11.44, -10.56}, {}}));
			var v_seq_48: seq<bool> := [false];
			var v_int_112: int := 8;
			var v_seq_49: seq<bool> := [true, false];
			var v_int_113: int := 9;
			var v_seq_50: seq<bool> := [true, true, true];
			var v_int_114: int := 8;
			if ((if ((v_multiset_3 in v_map_38)) then (v_map_38[v_multiset_3]) else ((if ((|v_seq_48| > 0)) then (v_seq_48[v_int_112]) else (true)))) == (match true {
				case _ => (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_114]) else (true))
			})) {
				var v_DT_1_1_9: DT_1 := DT_1_1;
				var v_DT_1_1_set_multiset_1: (DT_1, set<real>, multiset<int>) := (v_DT_1_1_9, {}, multiset{6});
				var v_DT_1_1_10: DT_1 := DT_1_1;
				var v_DT_1_1_set_multiset_2: (DT_1, set<real>, multiset<int>) := (v_DT_1_1_10, {8.33, 20.00}, multiset{5});
				var v_seq_51: seq<(DT_1, set<real>, multiset<int>)> := [v_DT_1_1_set_multiset_1, v_DT_1_1_set_multiset_2];
				var v_seq_53: seq<(DT_1, set<real>, multiset<int>)> := (if ((|v_seq_51| > 0)) then (v_seq_51[7..19]) else (v_seq_51));
				var v_seq_52: seq<int> := [];
				var v_int_115: int := 25;
				var v_seq_54: seq<(DT_1, set<real>, multiset<int>)> := (if ((|v_seq_53| > 0)) then (v_seq_53[(if ((|v_seq_52| > 0)) then (v_seq_52[v_int_115]) else (24))..0]) else (v_seq_53));
				var v_map_40: map<multiset<bool>, int> := (if (true) then (map[multiset{false, false, false} := 27, multiset{} := 15, multiset{true, true} := 3]) else (map[multiset{true} := 11, multiset{false, false} := 27, multiset{} := 16, multiset{} := 6]));
				var v_multiset_4: multiset<bool> := (if (false) then (multiset({true})) else (multiset({})));
				var v_map_39: map<bool, int> := map[true := 5, false := 6];
				var v_bool_23: bool := true;
				var v_int_116: int := (if ((v_multiset_4 in v_map_40)) then (v_map_40[v_multiset_4]) else ((if ((v_bool_23 in v_map_39)) then (v_map_39[v_bool_23]) else (-20))));
				var v_DT_1_1_11: DT_1 := DT_1_1;
				var v_DT_1_1_set_multiset_3: (DT_1, set<real>, multiset<int>) := (v_DT_1_1_11, {-9.02, -4.23, -25.51}, multiset{});
				var v_DT_1_1_12: DT_1 := DT_1_1;
				var v_DT_1_1_set_multiset_4: (DT_1, set<real>, multiset<int>) := (v_DT_1_1_12, {-8.71, 24.90, 17.95, 18.79}, multiset{19});
				var v_seq_55: seq<(DT_1, set<real>, multiset<int>)> := [v_DT_1_1_set_multiset_3, v_DT_1_1_set_multiset_4];
				var v_int_117: int := 6;
				var v_DT_1_1_13: DT_1 := DT_1_1;
				var v_DT_1_1_set_multiset_5: (DT_1, set<real>, multiset<int>) := (v_DT_1_1_13, {-26.47}, multiset{23, 26, 19, 17});
				var v_seq_56: seq<(DT_1, set<real>, multiset<int>)> := [];
				var v_int_118: int := 23;
				var v_DT_1_1_14: DT_1 := DT_1_1;
				var v_DT_1_1_set_multiset_6: (DT_1, set<real>, multiset<int>) := (v_DT_1_1_14, {}, multiset{22});
				var v_int_119: int, v_DT_1_1_set_multiset_7: (DT_1, set<real>, multiset<int>) := v_int_110, (if ((|v_seq_54| > 0)) then (v_seq_54[v_int_116]) else ((match 19.65 {
					case _ => (if ((|v_seq_56| > 0)) then (v_seq_56[v_int_118]) else (v_DT_1_1_set_multiset_6))
				})));
				var v_map_44: map<multiset<bool>, bool> := map[multiset({}) := false, multiset({true, true}) := true, multiset{false, true, true, false} := false][multiset{true, false, false, true} := false][(if (false) then (multiset({false, true, false, false})) else (multiset{false, false})) := (true || true)];
				var v_array_26: array<real> := new real[4] [-14.34, -3.26, 11.19, -22.91];
				var v_array_27: array<real> := new real[4] [-7.78, 7.45, 15.73, -17.02];
				var v_array_28: array<real> := new real[3] [-21.95, -19.62, 12.14];
				var v_array_29: array<real> := new real[3] [-4.38, 22.96, 15.05];
				var v_array_30: array<real> := new real[4] [-8.65, -29.43, -11.02, 6.23];
				var v_map_41: map<array<real>, multiset<bool>> := map[v_array_26 := multiset{false, false, false, false}, v_array_27 := multiset{false, true}, v_array_28 := multiset{true}, v_array_29 := multiset{}, v_array_30 := multiset({})];
				var v_array_31: array<real> := new real[4] [9.08, 1.57, -29.42, 8.64];
				var v_array_32: array<real> := v_array_31;
				var v_multiset_5: multiset<bool> := ((if ((v_array_32 in v_map_41)) then (v_map_41[v_array_32]) else (multiset{true, false})) * (if (false) then (multiset{false, false}) else (multiset({false, false, false}))));
				var v_real_bool_1: (real, bool) := (6.86, true);
				var v_DT_2_1_1: DT_2<int, bool> := DT_2_1;
				var v_multiset_real_bool_DT_2_1_1: (multiset<int>, (real, bool), DT_2<int, bool>) := (multiset{16, 2}, v_real_bool_1, v_DT_2_1_1);
				var v_real_bool_2: (real, bool) := (-2.05, false);
				var v_DT_2_1_2: DT_2<int, bool> := DT_2_1;
				var v_multiset_real_bool_DT_2_1_2: (multiset<int>, (real, bool), DT_2<int, bool>) := (multiset{8, 22, 21, 6}, v_real_bool_2, v_DT_2_1_2);
				var v_real_bool_3: (real, bool) := (11.95, false);
				var v_DT_2_1_3: DT_2<int, bool> := DT_2_1;
				var v_multiset_real_bool_DT_2_1_3: (multiset<int>, (real, bool), DT_2<int, bool>) := (multiset{10}, v_real_bool_3, v_DT_2_1_3);
				var v_real_bool_4: (real, bool) := (-8.59, true);
				var v_DT_2_1_4: DT_2<int, bool> := DT_2_1;
				var v_multiset_real_bool_DT_2_1_4: (multiset<int>, (real, bool), DT_2<int, bool>) := (multiset{}, v_real_bool_4, v_DT_2_1_4);
				var v_real_bool_5: (real, bool) := (-21.37, false);
				var v_DT_2_1_5: DT_2<int, bool> := DT_2_1;
				var v_multiset_real_bool_DT_2_1_5: (multiset<int>, (real, bool), DT_2<int, bool>) := (multiset{1}, v_real_bool_5, v_DT_2_1_5);
				var v_map_42: map<(multiset<int>, (real, bool), DT_2<int, bool>), bool> := map[v_multiset_real_bool_DT_2_1_1 := false, v_multiset_real_bool_DT_2_1_2 := true, v_multiset_real_bool_DT_2_1_3 := true, v_multiset_real_bool_DT_2_1_4 := true, v_multiset_real_bool_DT_2_1_5 := false];
				var v_real_bool_6: (real, bool) := (-23.96, true);
				var v_DT_2_1_6: DT_2<int, bool> := DT_2_1;
				var v_multiset_real_bool_DT_2_1_6: (multiset<int>, (real, bool), DT_2<int, bool>) := (multiset{23, 17, 10}, v_real_bool_6, v_DT_2_1_6);
				var v_multiset_real_bool_DT_2_1_7: (multiset<int>, (real, bool), DT_2<int, bool>) := v_multiset_real_bool_DT_2_1_6;
				var v_seq_57: seq<bool> := [false, false];
				var v_int_120: int := 10;
				var v_map_43: map<seq<bool>, bool> := map[[false, false] := true];
				var v_seq_58: seq<bool> := [];
				match (if ((v_multiset_5 in v_map_44)) then (v_map_44[v_multiset_5]) else ((if ((if ((v_multiset_real_bool_DT_2_1_7 in v_map_42)) then (v_map_42[v_multiset_real_bool_DT_2_1_7]) else (false))) then ((if ((|v_seq_57| > 0)) then (v_seq_57[v_int_120]) else (false))) else ((if ((v_seq_58 in v_map_43)) then (v_map_43[v_seq_58]) else (true)))))) {
					case _ => {
						return ;
					}
					
				}
				
			}
		}
		return ;
	}
	var v_DT_1_1_15: DT_1 := DT_1_1;
	var v_DT_1_1_16: DT_1 := DT_1_1;
	var v_DT_1_1_17: DT_1 := DT_1_1;
	var v_DT_1_1_18: DT_1 := DT_1_1;
	var v_DT_1_1_19: DT_1 := DT_1_1;
	var v_DT_1_1_20: DT_1 := DT_1_1;
	var v_map_45: map<DT_1, bool> := map[v_DT_1_1_15 := false, v_DT_1_1_16 := false, v_DT_1_1_17 := false, v_DT_1_1_18 := false, v_DT_1_1_19 := false][v_DT_1_1_20 := false];
	var v_DT_1_1_21: DT_1 := DT_1_1;
	var v_DT_1_1_22: DT_1 := DT_1_1;
	var v_DT_1_1_23: DT_1 := (if (false) then (v_DT_1_1_21) else (v_DT_1_1_22));
	var v_map_47: map<int, bool> := map[8 := false, 4 := true, 8 := false][13 := true];
	var v_int_121: int := (3 + -6);
	var v_map_46: map<char, bool> := map['C' := true, 'x' := false, 'A' := false, 's' := false, 'q' := false];
	var v_char_2: char := 'F';
	if (if ((if ((v_DT_1_1_23 in v_map_45)) then (v_map_45[v_DT_1_1_23]) else ((match 8 {
		case _ => true
	})))) then (((if (true) then (true) else (false)) || (if (true) then (false) else (false)))) else ((if ((v_int_121 in v_map_47)) then (v_map_47[v_int_121]) else ((if ((v_char_2 in v_map_46)) then (v_map_46[v_char_2]) else (false)))))) {
		
	}
	assert true;
	expect true;
	var v_map_48: map<multiset<multiset<int>>, int> := map[multiset{multiset{8, 1}, multiset{1, 18}, multiset{-24, 15, 8}} := 25, multiset{} := 13, multiset{multiset{-26, 0}, multiset{25, 3, 21, 26}, multiset{16, 26, 2}, multiset({13})} := 9, multiset{} := 29];
	var v_multiset_6: multiset<multiset<int>> := multiset({multiset{6}, multiset{}});
	var v_map_49: map<int, char> := (map[5 := 'W'] - {9, 15, 0})[(if ((v_multiset_6 in v_map_48)) then (v_map_48[v_multiset_6]) else (18)) := (match 1 {
		case _ => 'y'
	})];
	var v_int_123: int := v_int_10;
	var v_seq_59: seq<char> := ['y'];
	var v_int_122: int := 26;
	match (if ((v_int_123 in v_map_49)) then (v_map_49[v_int_123]) else ((match 22 {
		case _ => (match -20.96 {
			case _ => 'd'
		})
	}))) {
		case _ => {
			var v_seq_74: seq<bool> := (if (true) then ([true]) else ([true, true, false]));
			var v_seq_75: seq<bool> := v_seq_74;
			var v_int_142: int := (8 / 21);
			var v_int_143: int := safe_index_seq(v_seq_75, v_int_142);
			var v_int_144: int := v_int_143;
			var v_map_59: map<bool, bool> := map[false := true, true := false, true := true, false := true];
			var v_bool_30: bool := false;
			var v_seq_76: seq<bool> := (if ((|v_seq_74| > 0)) then (v_seq_74[v_int_144 := (if ((v_bool_30 in v_map_59)) then (v_map_59[v_bool_30]) else (false))]) else (v_seq_74));
			var v_int_145: int := ((13 + 26) % (if (false) then (1) else (14)));
			var v_map_60: map<int, bool> := (map[28 := true, 5 := false, 17 := false, 26 := true] - {6, 1});
			var v_int_146: int := (match 5 {
				case _ => 3
			});
			var v_seq_77: seq<bool> := [true];
			var v_seq_79: seq<bool> := (if ((|v_seq_77| > 0)) then (v_seq_77[12..29]) else (v_seq_77));
			var v_seq_78: seq<int> := [15, 8];
			var v_int_147: int := 25;
			var v_seq_81: seq<bool> := (if ((|v_seq_79| > 0)) then (v_seq_79[(if ((|v_seq_78| > 0)) then (v_seq_78[v_int_147]) else (28))..(if (true) then (21) else (-6))]) else (v_seq_79));
			var v_seq_80: seq<int> := [];
			var v_int_148: int := 29;
			var v_int_149: int := (match 5 {
				case _ => (match 27 {
					case _ => 6
				})
			});
			var v_map_61: map<int, bool> := map[24 := false];
			var v_int_150: int := 21;
			var v_seq_82: seq<bool> := [true, false, true, true];
			var v_seq_83: seq<bool> := (if ((|v_seq_82| > 0)) then (v_seq_82[29..17]) else (v_seq_82));
			var v_seq_85: seq<bool> := (if ((|v_seq_83| > 0)) then (v_seq_83[v_int_143..(8 * 29)]) else (v_seq_83));
			var v_seq_84: seq<bool> := [false, false, true];
			var v_int_151: int := 28;
			var v_int_152: int := (if ((if ((|v_seq_84| > 0)) then (v_seq_84[v_int_151]) else (true))) then (v_int_144) else ((-12.07).Floor));
			var v_bool_31: bool, v_bool_32: bool, v_bool_33: bool, v_bool_34: bool, v_bool_35: bool := (if ((|v_seq_76| > 0)) then (v_seq_76[v_int_145]) else ((if ((v_int_146 in v_map_60)) then (v_map_60[v_int_146]) else ((if (true) then (true) else (true)))))), (if ((|v_seq_81| > 0)) then (v_seq_81[v_int_149]) else ((if ((match 1 {
				case _ => false
			})) then ((if ((v_int_150 in v_map_61)) then (v_map_61[v_int_150]) else (false))) else (([17, 25, 4, 29] == []))))), v_bool_30, (if ((|v_seq_85| > 0)) then (v_seq_85[v_int_152]) else (((false && false) <==> (match 23 {
				case _ => true
			})))), ((match 11 {
				case _ => v_int_151
			}) >= ((if (false) then (10) else (8)) + (16 - 2)));
			var v_seq_86: seq<bool> := [];
			var v_seq_87: seq<bool> := (if ((|v_seq_86| > 0)) then (v_seq_86[11..-25]) else (v_seq_86));
			var v_int_154: int := (10 % 0);
			var v_map_62: map<int, bool> := map[-8 := true, 11 := true, 24 := true];
			var v_int_155: int := 12;
			var v_seq_88: seq<int> := [23, 25, 17, 7];
			var v_int_156: int := 18;
			var v_seq_89: seq<int> := [9, 17];
			var v_int_157: int := 13;
			var v_map_63: map<int, int> := map[28 := 14, 23 := 2, 27 := 17];
			var v_int_158: int := 12;
			var v_seq_90: seq<int> := [];
			var v_int_159: int := 12;
			var v_seq_91: seq<int> := [2];
			var v_seq_93: seq<int> := (if ((|v_seq_91| > 0)) then (v_seq_91[-5..0]) else (v_seq_91));
			var v_seq_92: seq<int> := [22, 2];
			var v_int_160: int := 28;
			var v_int_161: int := (if ((|v_seq_92| > 0)) then (v_seq_92[v_int_160]) else (16));
			var v_int_163: int, v_int_164: int := (if ((if ((|v_seq_87| > 0)) then (v_seq_87[v_int_154]) else ((if ((v_int_155 in v_map_62)) then (v_map_62[v_int_155]) else (false))))) then (v_int_146) else ((match 0 {
				case _ => v_int_11
			}))), (if (v_bool_30) then ((match 28 {
				case _ => (if ((|v_seq_90| > 0)) then (v_seq_90[v_int_159]) else (13))
			})) else ((if ((|v_seq_93| > 0)) then (v_seq_93[v_int_161]) else (v_int_143))));
			for v_int_153 := v_int_163 to v_int_164 
				invariant (v_int_164 - v_int_153 >= 0)
			{
				var v_seq_94: seq<bool> := [false, false, false];
				var v_int_162: int := 9;
				if ((match 5 {
					case _ => v_bool_33
				}) || (if ((if ((|v_seq_94| > 0)) then (v_seq_94[v_int_162]) else (true))) then ((if (true) then (true) else (false))) else (v_bool_31))) {
					break;
				} else {
					return ;
				}
			}
			return ;
		}
		
	}
	
}
