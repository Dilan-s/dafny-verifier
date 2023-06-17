datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_2(DT_1_2_1: multiset<real>, DT_1_2_2: T_1, DT_1_2_3: T_2) | DT_1_3 | DT_1_4(DT_1_4_1: T_1, DT_1_4_2: seq<bool>)
datatype DT_2 = DT_2_1
datatype DT_3<T_3, T_4> = DT_3_1
datatype DT_4<T_5, T_6> = DT_4_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_7(p_m_method_7_1: array<bool>, p_m_method_7_2: DT_1<DT_1<bool, bool>, real>, p_m_method_7_3: bool, p_m_method_7_4: bool) returns (ret_1: seq<(int, char)>)
{
	var v_int_34: int, v_bool_6: bool, v_real_17: real := 14, true, -9.20;
	var v_int_char_4: (int, char) := (10, 'z');
	var v_int_char_5: (int, char) := (1, 'G');
	var v_int_char_6: (int, char) := (9, 'k');
	var v_int_char_7: (int, char) := (14, 'B');
	return [v_int_char_4, v_int_char_5, v_int_char_6, v_int_char_7];
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: (bool, int)) returns (ret_1: real)
{
	return -27.65;
}

method m_method_5(p_m_method_5_1: bool, p_m_method_5_2: bool, p_m_method_5_3: char) returns (ret_1: real)
{
	return 1.27;
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: (bool, int, int), p_m_method_4_3: map<int, bool>) returns (ret_1: int)
{
	return -20;
}

method m_method_3(p_m_method_3_1: real) returns (ret_1: bool)
	requires ((9.18 < p_m_method_3_1 < 9.38));
	ensures (((9.18 < p_m_method_3_1 < 9.38)) ==> ((ret_1 == true)));
{
	var v_real_11: real, v_real_12: real := -7.20, -0.06;
	print "v_real_11", " ", (v_real_11 == -7.20), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 9.28), " ", "v_real_12", " ", (v_real_12 == -0.06), "\n";
	return true;
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

method m_method_2(p_m_method_2_1: array<real>, p_m_method_2_2: char) returns (ret_1: real, ret_2: real)
	requires ((p_m_method_2_2 == 'n') && p_m_method_2_1.Length == 4 && (-11.27 < p_m_method_2_1[0] < -11.07) && (-19.48 < p_m_method_2_1[1] < -19.28) && (19.27 < p_m_method_2_1[2] < 19.47) && (8.01 < p_m_method_2_1[3] < 8.21));
	ensures (((p_m_method_2_2 == 'n') && p_m_method_2_1.Length == 4 && (-11.27 < p_m_method_2_1[0] < -11.07) && (-19.48 < p_m_method_2_1[1] < -19.28) && (19.27 < p_m_method_2_1[2] < 19.47) && (8.01 < p_m_method_2_1[3] < 8.21)) ==> ((-16.85 < ret_1 < -16.65) && (-9.99 < ret_2 < -9.79)));
{
	print "p_m_method_2_1", " ", "p_m_method_2_1[2]", " ", (p_m_method_2_1[2] == 19.37), " ", "p_m_method_2_1[0]", " ", (p_m_method_2_1[0] == -11.17), " ", "p_m_method_2_1[1]", " ", (p_m_method_2_1[1] == -19.38), " ", "p_m_method_2_2", " ", (p_m_method_2_2 == 'n'), "\n";
	return -16.75, -9.89;
}

method m_method_1(p_m_method_1_1: real, p_m_method_1_2: real) returns (ret_1: bool)
	requires ((-3.74 < p_m_method_1_1 < -3.54) && (1.76 < p_m_method_1_2 < 1.96));
	ensures (((-3.74 < p_m_method_1_1 < -3.54) && (1.76 < p_m_method_1_2 < 1.96)) ==> ((ret_1 == false)));
{
	var v_int_14: int := 4;
	var v_int_15: int := 2;
	while (v_int_14 < v_int_15) 
		decreases v_int_15 - v_int_14;
		invariant (v_int_14 <= v_int_15);
	{
		v_int_14 := (v_int_14 + 1);
		assert true;
		expect true;
		var v_int_17: int, v_int_18: int := 9, 10;
		for v_int_16 := v_int_17 to v_int_18 
			invariant (v_int_18 - v_int_16 >= 0)
		{
			return true;
		}
		assert true;
		expect true;
		assert true;
		expect true;
	}
	assert ((v_int_14 == 4) && (p_m_method_1_2 == 1.86) && (p_m_method_1_1 == -3.64) && (v_int_15 == 2));
	expect ((v_int_14 == 4) && (p_m_method_1_2 == 1.86) && (p_m_method_1_1 == -3.64) && (v_int_15 == 2));
	var v_real_6: real := 0.03;
	assert ((v_int_14 == 4));
	expect ((v_int_14 == 4));
	var v_array_1: array<real> := new real[4] [-11.17, -19.38, 19.37, 8.11];
	var v_array_2: array<real> := v_array_1;
	var v_char_1: char := 'n';
	var v_real_7: real, v_real_8: real := m_method_2(v_array_2, v_char_1);
	v_real_6, v_array_1[3] := v_real_7, v_real_8;
	assert ((v_array_1[0] == -11.17) && (v_int_15 == 2) && (p_m_method_1_2 == 1.86) && (v_array_1[1] == -19.38) && (p_m_method_1_1 == -3.64));
	expect ((v_array_1[0] == -11.17) && (v_int_15 == 2) && (p_m_method_1_2 == 1.86) && (v_array_1[1] == -19.38) && (p_m_method_1_1 == -3.64));
	print "v_char_1", " ", (v_char_1 == 'n'), " ", "v_real_8", " ", (v_real_8 == -9.89), " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 1.86), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == -3.64), " ", "v_int_15", " ", v_int_15, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_int_14", " ", v_int_14, " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[1]", " ", (v_array_1[1] == -19.38), " ", "v_array_1[2]", " ", (v_array_1[2] == 19.37), " ", "v_array_1[0]", " ", (v_array_1[0] == -11.17), " ", "v_real_6", " ", (v_real_6 == -16.75), " ", "v_array_1[3]", " ", (v_array_1[3] == -9.89), " ", "v_real_7", " ", (v_real_7 == -16.75), "\n";
	return false;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_1: map<multiset<real>, int> := map[multiset{-19.50} := 21, multiset({27.32, -19.67, -7.21, -28.45}) := 21];
	var v_multiset_1: multiset<real> := multiset{5.90, 2.87, -6.14};
	var v_int_7: int := (1 / ((if ((v_multiset_1 in v_map_1)) then (v_map_1[v_multiset_1]) else (10)) - (if (false) then (0) else (8))));
	var v_map_2: map<real, char> := map[28.70 := 'h'];
	var v_real_1: real := 12.62;
	var v_map_3: map<real, seq<int>> := map[15.64 := [8], 16.83 := [], -12.14 := [20]];
	var v_real_2: real := -6.84;
	var v_seq_3: seq<int> := (if ((v_real_2 in v_map_3)) then (v_map_3[v_real_2]) else ([16, 14, -22]));
	var v_int_9: int := (match -11.79 {
		case 14.52 => 8
		case _ => 14
	});
	var v_seq_20: seq<int> := v_seq_3;
	var v_int_41: int := v_int_9;
	var v_int_42: int := safe_index_seq(v_seq_20, v_int_41);
	v_int_9 := v_int_42;
	var v_int_8: int := (if (((if ((v_real_1 in v_map_2)) then (v_map_2[v_real_1]) else ('n')) <= 'Q')) then (v_int_7) else ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_9]) else (v_int_9))));
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8) && ((((v_int_7 == 11)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 12)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 13)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 14)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 10)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 15)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 16)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 9)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 8)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 7)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 6)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 5)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 4)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 3)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 2)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 1)) ==> ((((-6.94 < v_real_2 < -6.74))))) && (((v_int_7 == 0)) ==> ((((-6.94 < v_real_2 < -6.74))))));
	{
		v_int_7 := (v_int_7 + 1);
		assert ((v_real_2 == -6.84));
		expect ((v_real_2 == -6.84));
		var v_map_4: map<real, set<real>> := map[12.71 := {-14.91, -5.45, -12.91, 12.14}, -12.77 := {17.35, 8.70}, 29.13 := {}];
		var v_real_3: real := -28.23;
		var v_map_6: map<real, int> := ((map[15.02 := 27, -1.63 := 0, 8.22 := 9, 13.22 := 25, -25.93 := -4] - {}) - (if ((v_real_3 in v_map_4)) then (v_map_4[v_real_3]) else ({})));
		var v_real_5: real := v_real_1;
		var v_seq_4: seq<real> := [3.70];
		var v_int_12: int := 25;
		var v_int_13: int := safe_index_seq(v_seq_4, v_int_12);
		var v_map_5: map<real, int> := map[4.46 := 14];
		var v_real_4: real := -2.19;
		var v_int_10: int := (if ((v_real_5 in v_map_6)) then (v_map_6[v_real_5]) else ((match -24.46 {
			case -26.20 => v_int_13
			case v_real_1 => (if ((v_real_4 in v_map_5)) then (v_map_5[v_real_4]) else (11))
			case _ => (if (false) then (10) else (17))
		})));
		var v_real_9: real := -3.64;
		var v_real_10: real := 1.86;
		var v_bool_1: bool := m_method_1(v_real_9, v_real_10);
		var v_real_13: real := 9.28;
		var v_bool_2: bool := m_method_3(v_real_13);
		var v_int_19: int := 7;
		var v_int_20: int := 21;
		var v_int_21: int := safe_division(v_int_19, v_int_20);
		var v_seq_5: seq<int> := [16];
		var v_int_22: int := 15;
		var v_int_11: int := (if ((if (v_bool_1) then (v_bool_1) else (v_bool_2))) then ((if (v_bool_2) then (v_int_21) else ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_22]) else (3))))) else (v_int_21));
		while (v_int_10 < v_int_11) 
			decreases v_int_11 - v_int_10;
			invariant (v_int_10 <= v_int_11) && ((((v_int_10 == 17)) ==> ((((-6.94 < v_real_2 < -6.74)) && ((9.18 < v_real_13 < 9.38))))));
		{
			v_int_10 := (v_int_10 + 1);
			var v_int_23: int := v_int_21;
			var v_int_24: int := v_int_19;
			while (v_int_23 < v_int_24) 
				decreases v_int_24 - v_int_23;
				invariant (v_int_23 <= v_int_24);
			{
				v_int_23 := (v_int_23 + 1);
				var v_char_char_seq_1: (char, char, seq<real>) := ('n', 'V', []);
				var v_map_7: map<(char, char, seq<real>), seq<real>> := map[v_char_char_seq_1 := [21.71]];
				var v_char_char_seq_2: (char, char, seq<real>) := ('O', 'u', [-26.64, 26.01, -3.66, 20.03]);
				var v_char_char_seq_3: (char, char, seq<real>) := v_char_char_seq_2;
				var v_seq_6: seq<real> := (if ((v_char_char_seq_3 in v_map_7)) then (v_map_7[v_char_char_seq_3]) else ([]));
				var v_bool_3: bool := false;
				var v_bool_int_int_1: (bool, int, int) := (true, 10, 3);
				var v_bool_int_int_2: (bool, int, int) := v_bool_int_int_1;
				var v_map_8: map<int, bool> := map[23 := false, 0 := true, 29 := false, 3 := true];
				var v_int_25: int := m_method_4(v_bool_3, v_bool_int_int_2, v_map_8);
				var v_int_26: int := v_int_25;
				var v_bool_4: bool := false;
				var v_bool_5: bool := false;
				var v_char_2: char := 'O';
				var v_real_14: real := m_method_5(v_bool_4, v_bool_5, v_char_2);
				var v_bool_int_1: (bool, int) := (false, 23);
				var v_bool_int_2: (bool, int) := v_bool_int_1;
				var v_real_15: real := m_method_6(v_bool_int_2);
				var v_map_10: map<int, int> := (if (false) then (map[6 := 19]) else (map[15 := -26, 19 := 7, 28 := 24, 27 := -9, 12 := -11]));
				var v_int_27: int := v_int_20;
				var v_real_bool_1: (real, bool) := (17.39, true);
				var v_DT_1_2_1: DT_1<real, real> := DT_1_2(multiset{24.18}, -2.61, 16.74);
				var v_real_bool_map_DT_1_2_1: ((real, bool), map<int, bool>, DT_1<real, real>) := (v_real_bool_1, map[1 := false, 8 := false, -19 := true, 8 := true, 0 := false], v_DT_1_2_1);
				var v_map_9: map<((real, bool), map<int, bool>, DT_1<real, real>), int> := map[v_real_bool_map_DT_1_2_1 := 21];
				var v_real_bool_2: (real, bool) := (16.74, false);
				var v_DT_1_2_2: DT_1<real, real> := DT_1_2(multiset{-4.76, -3.01, -26.76, 7.47}, -26.07, -12.77);
				var v_real_bool_map_DT_1_2_2: ((real, bool), map<int, bool>, DT_1<real, real>) := (v_real_bool_2, map[2 := true], v_DT_1_2_2);
				var v_real_bool_map_DT_1_2_3: ((real, bool), map<int, bool>, DT_1<real, real>) := v_real_bool_map_DT_1_2_2;
				v_real_2 := (match 9 {
					case _ => v_real_5
				});
				break;
			}
			var v_seq_7: seq<DT_2> := [];
			var v_int_28: int := 19;
			var v_DT_2_1_1: DT_2 := DT_2_1;
			var v_array_3: array<int> := new int[3] [14, 15, 14];
			var v_seq_array_1: (seq<bool>, array<int>) := ([false, true, false], v_array_3);
			var v_real_real_1: (real, real) := (13.51, 2.39);
			var v_real_real_2: (real, real) := (-12.40, 19.84);
			var v_array_4: array<int> := new int[4] [-14, 24, 13, -2];
			var v_seq_array_2: (seq<bool>, array<int>) := ([false, false, false], v_array_4);
			var v_real_real_3: (real, real) := (-12.61, -27.22);
			var v_array_5: array<int> := new int[5] [26, 10, 18, 11, 17];
			var v_seq_array_3: (seq<bool>, array<int>) := ([true, true], v_array_5);
			var v_real_real_4: (real, real) := (9.35, -23.65);
			var v_array_6: array<int> := new int[5] [13, 15, 29, 25, 27];
			var v_seq_array_4: (seq<bool>, array<int>) := ([false, true], v_array_6);
			var v_real_real_5: (real, real) := (11.15, -27.70);
			var v_real_real_6: (real, real) := (28.12, -19.60);
			var v_real_real_7: (real, real) := (-15.20, -0.08);
			var v_array_7: array<int> := new int[4] [18, 4, 27, 17];
			var v_seq_array_5: (seq<bool>, array<int>) := ([], v_array_7);
			var v_map_11: map<seq<(real, real)>, (seq<bool>, array<int>)> := map[[] := v_seq_array_1, [v_real_real_1, v_real_real_2] := v_seq_array_2, [v_real_real_3] := v_seq_array_3, [v_real_real_4] := v_seq_array_4, [v_real_real_5, v_real_real_6, v_real_real_7] := v_seq_array_5];
			var v_real_real_8: (real, real) := (-7.62, 23.78);
			var v_real_real_9: (real, real) := (-12.75, 27.88);
			var v_seq_8: seq<(real, real)> := [v_real_real_8, v_real_real_9];
			var v_array_8: array<int> := new int[3] [7, 23, 15];
			var v_seq_array_6: (seq<bool>, array<int>) := ([], v_array_8);
			var v_bool_int_3: (bool, int) := (false, 7);
			var v_bool_int_4: (bool, int) := v_bool_int_3;
			var v_real_16: real := m_method_6(v_bool_int_4);
			var v_array_9: array<int> := new int[5] [7, 8, 20, -27, 19];
			var v_seq_array_7: (seq<bool>, array<int>) := ([true, false], v_array_9);
			var v_array_10: array<int> := new int[5];
			v_array_10[0] := 7;
			v_array_10[1] := 29;
			v_array_10[2] := 4;
			v_array_10[3] := 12;
			v_array_10[4] := -10;
			var v_seq_array_8: (seq<bool>, array<int>) := ([false], v_array_10);
			var v_array_11: array<int> := new int[3];
			v_array_11[0] := 8;
			v_array_11[1] := 29;
			v_array_11[2] := 5;
			var v_seq_array_9: (seq<bool>, array<int>) := ([true, false, true], v_array_11);
			var v_array_12: array<int> := new int[4] [8, 18, 21, 3];
			var v_seq_array_10: (seq<bool>, array<int>) := ([true, false, true], v_array_12);
			var v_array_13: array<int> := new int[5] [21, 7, 12, 25, 9];
			var v_seq_array_11: (seq<bool>, array<int>) := ([true, false, false, true], v_array_13);
			var v_map_12: map<seq<real>, (seq<bool>, array<int>)> := map[[-29.62, -9.48] := v_seq_array_7, [-1.94, 9.98, 23.63, -11.12] := v_seq_array_8, [-3.76] := v_seq_array_9, [4.72, 22.12, -17.05] := v_seq_array_10, [19.61] := v_seq_array_11];
			var v_seq_9: seq<real> := [];
			var v_array_14: array<int> := new int[3] [2, 19, 20];
			var v_seq_array_12: (seq<bool>, array<int>) := ([false], v_array_14);
			var v_array_15: array<int> := new int[4] [12, 14, 21, 19];
			var v_seq_array_13: (seq<bool>, array<int>) := ([true], v_array_15);
			var v_array_16: array<int> := new int[5] [5, 8, 0, 4, -14];
			var v_seq_array_14: (seq<bool>, array<int>) := ([false, false, false, false], v_array_16);
			var v_seq_10: seq<(seq<bool>, array<int>)> := [];
			var v_seq_12: seq<(seq<bool>, array<int>)> := (if ((|v_seq_10| > 0)) then (v_seq_10[13..29]) else (v_seq_10));
			var v_seq_11: seq<int> := [14, 1];
			var v_int_29: int := 23;
			var v_int_30: int := safe_index_seq(v_seq_11, v_int_29);
			var v_int_31: int := v_int_30;
			var v_array_17: array<int> := new int[4] [28, 9, 23, 15];
			var v_seq_array_15: (seq<bool>, array<int>) := ([false], v_array_17);
			var v_array_18: array<int> := new int[3];
			v_array_18[0] := 10;
			v_array_18[1] := 20;
			v_array_18[2] := 24;
			var v_seq_array_16: (seq<bool>, array<int>) := ([false], v_array_18);
			var v_array_19: array<int> := new int[4] [-19, 2, 1, 12];
			var v_seq_array_17: (seq<bool>, array<int>) := ([], v_array_19);
			var v_seq_13: seq<(seq<bool>, array<int>)> := [v_seq_array_15, v_seq_array_16, v_seq_array_17];
			var v_int_32: int := 21;
			var v_array_20: array<int> := new int[3] [11, 10, 21];
			var v_seq_array_18: (seq<bool>, array<int>) := ([], v_array_20);
			var v_int_char_1: (int, char) := (-26, 'J');
			var v_int_char_2: (int, char) := (13, 'C');
			var v_int_char_3: (int, char) := (19, 'v');
			var v_seq_14: seq<(int, char)> := ([v_int_char_1] + [v_int_char_2, v_int_char_3]);
			var v_seq_15: seq<(int, char)> := (if ((|v_seq_14| > 0)) then (v_seq_14[v_array_20[1]..0]) else (v_seq_14));
			var v_int_33: int := v_int_23;
			var v_array_21: array<bool> := new bool[5] [true, true, true, true, false];
			var v_array_22: array<bool> := v_array_21;
			var v_DT_1_3_1: DT_1<bool, bool> := DT_1_3;
			var v_DT_1_4_1: DT_1<DT_1<bool, bool>, real> := DT_1_4(v_DT_1_3_1, [true, true]);
			var v_DT_1_4_2: DT_1<DT_1<bool, bool>, real> := v_DT_1_4_1;
			var v_bool_7: bool := false;
			var v_bool_8: bool := true;
			var v_seq_16: seq<(int, char)> := m_method_7(v_array_22, v_DT_1_4_2, v_bool_7, v_bool_8);
			var v_seq_17: seq<(int, char)> := v_seq_16;
			var v_int_35: int := 18;
			var v_int_36: int := 0;
			var v_int_37: int := safe_division(v_int_35, v_int_36);
			var v_int_38: int := v_int_37;
			var v_int_char_8: (int, char) := (10, 'f');
			var v_int_char_9: (int, char) := (19, 'G');
			var v_int_char_10: (int, char) := (-21, 'A');
			var v_seq_18: seq<(int, char)> := [v_int_char_8, v_int_char_9, v_int_char_10];
			var v_int_39: int := 25;
			var v_int_char_11: (int, char) := (4, 'G');
			var v_bool_int_5: (bool, int) := (true, 22);
			var v_bool_int_6: (bool, int) := (true, 7);
			var v_bool_int_7: (bool, int) := (false, 3);
			var v_bool_int_8: (bool, int) := (true, 15);
			var v_bool_int_9: (bool, int) := (false, 2);
			var v_bool_int_10: (bool, int) := (true, 24);
			var v_seq_19: seq<(bool, int)> := ([v_bool_int_5, v_bool_int_6, v_bool_int_7] + [v_bool_int_8, v_bool_int_9, v_bool_int_10]);
			var v_array_23: array<bool> := new bool[5];
			v_array_23[0] := true;
			v_array_23[1] := true;
			v_array_23[2] := true;
			v_array_23[3] := false;
			v_array_23[4] := false;
			var v_DT_4_1_1: DT_4<int, int> := DT_4_1;
			var v_array_map_DT_4_1_1: (array<bool>, map<bool, real>, DT_4<int, int>) := (v_array_23, map[true := 27.01, true := -25.16, false := 2.21], v_DT_4_1_1);
			var v_map_13: map<(array<bool>, map<bool, real>, DT_4<int, int>), int> := map[v_array_map_DT_4_1_1 := 19];
			var v_array_24: array<bool> := new bool[4] [false, false, true, false];
			var v_DT_4_1_2: DT_4<int, int> := DT_4_1;
			var v_array_map_DT_4_1_2: (array<bool>, map<bool, real>, DT_4<int, int>) := (v_array_24, map[true := -16.92, true := -2.69, true := -17.76, false := 7.82], v_DT_4_1_2);
			var v_array_map_DT_4_1_3: (array<bool>, map<bool, real>, DT_4<int, int>) := v_array_map_DT_4_1_2;
			var v_int_40: int := (if ((v_array_map_DT_4_1_3 in v_map_13)) then (v_map_13[v_array_map_DT_4_1_3]) else (25));
			var v_bool_int_11: (bool, int) := (false, 5);
			var v_bool_int_12: (bool, int) := (false, 21);
			var v_bool_int_13: (bool, int) := (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_40]) else ((match false {
				case _ => v_bool_int_12
			})));
			var v_real_18: real := m_method_6(v_bool_int_13);
			v_seq_array_18, v_int_char_8, v_real_13 := (if (((if ((|v_seq_7| > 0)) then (v_seq_7[v_int_28]) else (v_DT_2_1_1)) !in v_seq_7)) then ((match -4.27 {
				case _ => (if (true) then (v_seq_array_13) else (v_seq_array_14))
			})) else ((if ((|v_seq_12| > 0)) then (v_seq_12[v_int_31]) else ((if ((|v_seq_13| > 0)) then (v_seq_13[v_int_32]) else (v_seq_array_18)))))), (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_33]) else ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_38]) else ((if ((|v_seq_18| > 0)) then (v_seq_18[v_int_39]) else (v_int_char_11)))))), v_real_18;
		}
		print "v_bool_1", " ", v_bool_1, " ", "v_map_4", " ", (v_map_4 == map[29.13 := {}, -12.77 := {8.70, 17.35}, 12.71 := {-14.91, -5.45, 12.14, -12.91}]), " ", "v_real_9", " ", (v_real_9 == -3.64), " ", "v_map_6", " ", (v_map_6 == map[-1.63 := 0, 13.22 := 25, 15.02 := 27, -25.93 := -4, 8.22 := 9]), " ", "v_bool_2", " ", v_bool_2, " ", "v_int_19", " ", v_int_19, " ", "v_int_22", " ", v_int_22, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_real_10", " ", (v_real_10 == 1.86), " ", "v_int_21", " ", v_int_21, " ", "v_seq_5", " ", v_seq_5, " ", "v_real_3", " ", (v_real_3 == -28.23), " ", "v_int_20", " ", v_int_20, " ", "v_real_5", " ", (v_real_5 == 12.62), " ", "v_real_13", " ", (v_real_13 == 9.28), " ", "v_seq_3", " ", v_seq_3, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_real_1", " ", (v_real_1 == 12.62), " ", "v_real_2", " ", (v_real_2 == -6.84), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{5.90, -6.14, 2.87}), " ", "v_map_1", " ", (v_map_1 == map[multiset{-19.50} := 21, multiset{-7.21, 27.32, -28.45, -19.67} := 21]), " ", "v_map_3", " ", (v_map_3 == map[15.64 := [8], -12.14 := [20], 16.83 := []]), " ", "v_map_2", " ", (v_map_2 == map[28.70 := 'h']), "\n";
	}
	print "v_seq_3", " ", v_seq_3, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_real_1", " ", (v_real_1 == 12.62), " ", "v_real_2", " ", (v_real_2 == -6.84), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{5.90, -6.14, 2.87}), " ", "v_map_1", " ", (v_map_1 == map[multiset{-19.50} := 21, multiset{-7.21, 27.32, -28.45, -19.67} := 21]), " ", "v_map_3", " ", (v_map_3 == map[15.64 := [8], -12.14 := [20], 16.83 := []]), " ", "v_map_2", " ", (v_map_2 == map[28.70 := 'h']), "\n";
}
