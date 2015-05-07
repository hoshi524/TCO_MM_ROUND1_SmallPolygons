import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;

/**
 * tomerunさんのコードで勉強する
 */
public class SmallPolygonsTomerun {

	private static final boolean DEBUG = 1 == 0;
	private static final boolean MEASURE_TIME = 1 == 0;
	private static final long TL = 8000;
	long startTime = System.currentTimeMillis(), worstTime;
	Timer timer = new Timer();
	Counter counter = new Counter();
	XorShift rnd = new XorShift();
	Point[] ps, i2p;
	int P, N;
	TriangleSet triSet;
	ArrayList<ArrayList<Point>> bestAns = new ArrayList<>();
	int bestScore = Integer.MAX_VALUE;
	double initialHeat, heatMul;

	String[] choosePolygons(int[] points, int N) {
		this.P = points.length / 2;
		this.N = Math.min(N, P / 3);
		this.ps = new Point[P];
		for (int i = 0; i < P; ++i) {
			ps[i] = new Point(points[2 * i], points[2 * i + 1], i);
		}
		this.i2p = new Point[P];
		for (int i = 0; i < P; ++i) {
			this.i2p[ps[i].id] = ps[i];
		}
		Arrays.sort(ps);

		if (P <= 30 && P / 3 == this.N) {
			initialHeat = 800000.0 / P;
			heatMul = 0.95;
			solveSA(TL / 3);
			solveBrute();
		} else if (P <= N * 5) {
			initialHeat = 800000.0 / P;
			heatMul = 0.9;
			int LOOP = P <= N * 3.5 ? 7 : 4;
			int optimalScore = Integer.MAX_VALUE;
			ArrayList<ArrayList<Point>> optimalAns = null;
			long PREMIUM_FIRST = 300;
			for (int i = 1; i <= LOOP; ++i) {
				solveSA((TL - PREMIUM_FIRST) * i / (LOOP) + PREMIUM_FIRST);
				if (bestScore < optimalScore) {
					optimalScore = bestScore;
					optimalAns = new ArrayList<>(bestAns);
				}
				triSet.shuffle(rnd);
			}
			bestAns = optimalAns;
			bestScore = optimalScore;
			//			State bestState = new State(P);
			//			for (int i = 0; i < bestAns.size(); ++i) {
			//				Polygon poly = new Polygon(bestAns.get(i));
			//				bestState.add(poly);
			//			}
			//			initialHeat = 200000.0 / P;
			//			heatMul = 0.9;
			//			globalImprove(bestState, TL);
			//			if (bestState.val < bestScore) {
			//				bestScore = bestState.val;
			//				debug("improved area:" + bestState.val);
			//				bestAns.clear();
			//				for (Polygon bestPoly : bestState.poly) {
			//					bestAns.add(bestPoly.v);
			//				}
			//			}
		} else if (P <= Math.min(600, 300 + N * 50) || (N > 16 && P <= 360 + 15 * N)) {
			initialHeat = 800000.0 / P;
			heatMul = P >= 500 ? 0.96 : 0.95;
			solveSA(TL);
		} else {
			solveVoronoi(TL);
		}

		String[] ansStr = new String[bestAns.size()];
		for (int i = 0; i < bestAns.size(); ++i) {
			ArrayList<Point> curAns = bestAns.get(i);
			ansStr[i] = curAns.get(0).id + "";
			for (int j = 1; j < curAns.size(); ++j) {
				ansStr[i] += " " + curAns.get(j).id;
			}
		}
		if (DEBUG) {
			int[] vcnt = new int[bestAns.size()];
			for (int i = 0; i < bestAns.size(); ++i) {
				vcnt[i] = bestAns.get(i).size();
			}
			Arrays.sort(vcnt);
			System.err.print("used N:" + vcnt.length + " [");
			for (int i = 0; i < vcnt.length; ++i) {
				System.err.print(vcnt[i] + " ");
			}
			System.err.println("]");
			timer.print();
			counter.print();
		}
		return ansStr;
	}

	int[] polyIdx;
	int recCnt = 0;
	boolean recTimeout = false;

	void solveBrute() {
		timer.start(0);
		polyIdx = new int[P];
		Arrays.fill(polyIdx, -1);
		if (triSet == null) {
			triSet = enumeratePolys();
		}
		Collections.sort(triSet.tris);
		timer.stop(0);
		State state = new State(P);
		recBrute(state, 0, 0);
		debug("recCnt:" + recCnt);
	}

	void recBrute(State st, int useCnt, int triPos) {
		if (st.val >= bestScore) return;
		if (useCnt == P) {
			bestScore = st.val;
			bestAns.clear();
			for (Polygon bestPoly : st.poly) {
				bestAns.add(bestPoly.v);
			}
			debug("best area:" + st.val);
			return;
		}
		++recCnt;
		if ((recCnt & 0xFFF) == 0 && System.currentTimeMillis() - startTime > TL) {
			recTimeout = true;
		}
		if (recTimeout) return;
		final int maxAdd = Math.min((P - useCnt) / 3, N - st.poly.size());
		final int minAppend = (P - useCnt) - 3 * maxAdd + maxAdd;
		final int pruneTh = (bestScore - st.val) / minAppend;
		for (int i = triPos; i < triSet.tris.size(); ++i) {
			Polygon curTri = triSet.tris.get(i);
			if (curTri.area >= pruneTh) {
				break;
			}
			Point p1 = curTri.v.get(0);
			Point p2 = curTri.v.get(1);
			Point p3 = curTri.v.get(2);
			final int poi1 = polyIdx[p1.id];
			final int poi2 = polyIdx[p2.id];
			final int poi3 = polyIdx[p3.id];
			final int n = st.poly.size();
			int used = 0;
			if (poi1 != -1) ++used;
			if (poi2 != -1) ++used;
			if (poi3 != -1) ++used;

			// add new triangle
			if (used == 0 && n < N) {
				final boolean cross = cross(st, curTri);
				if (!cross) {
					polyIdx[p1.id] = n;
					polyIdx[p2.id] = n;
					polyIdx[p3.id] = n;
					st.poly.add(curTri);
					st.val += curTri.area;
					recBrute(st, useCnt + 3, i + 1);
					st.val -= curTri.area;
					st.poly.remove(st.poly.size() - 1);
					polyIdx[p1.id] = -1;
					polyIdx[p2.id] = -1;
					polyIdx[p3.id] = -1;
				}
			}

			// append to existent polygon
			if (used != 2) continue;
			int poi = -1;
			if (poi1 == -1 && poi2 != -1 && poi2 == poi3) {
				Point tmp = p1;
				p1 = p3;
				p3 = p2;
				p2 = tmp;
				poi = poi2;
			} else if (poi2 == -1 && poi3 != -1 && poi3 == poi1) {
				poi = poi3;
			} else if (poi3 == -1 && poi1 != -1 && poi1 == poi2) {
				Point tmp = p3;
				p3 = p1;
				p1 = p2;
				p2 = tmp;
				poi = poi1;
			}
			if (poi != -1) {
				boolean ok = true;
				int insertPos = -1;
				Polygon appendPoly = st.poly.get(poi);
				for (int v1 = 0; v1 < appendPoly.v.size(); ++v1) {
					final int v2 = v1 == appendPoly.v.size() - 1 ? 0 : v1 + 1;
					final Point vp1 = appendPoly.v.get(v1);
					final Point vp2 = appendPoly.v.get(v2);
					final int vi1 = vp1.id;
					final int vi2 = vp2.id;
					if (vi1 == p1.id) {
						if (vi2 != p3.id) {
							ok = false;
							break;
						}
						insertPos = v1 + 1;
						continue;
					}
					if (vi2 != p1.id && cross(p1, p2, vp1, vp2)) {
						ok = false;
						break;
					}
					if (vi1 != p3.id && cross(p2, p3, vp1, vp2)) {
						ok = false;
						break;
					}
				}

				if (ok) {
					for (int j = 0; j < n; ++j) {
						if (j == poi) continue;
						Polygon crossPoly = st.poly.get(j);
						if (cross(crossPoly, p1, p2) || cross(crossPoly, p2, p3)) {
							ok = false;
							break;
						}
					}
				}
				if (ok) {
					Polygon op = st.poly.get(poi);
					Polygon np = op.add(p2, insertPos, curTri.area);
					polyIdx[p2.id] = poi;
					st.poly.set(poi, np);
					st.val += curTri.area;
					recBrute(st, useCnt + 1, i + 1);
					st.val -= curTri.area;
					st.poly.set(poi, op);
					polyIdx[p2.id] = -1;
				}
			}
		}
	}

	void solveSA(final long timelimit) {
		timer.start(0);
		if (triSet == null) {
			triSet = enumeratePolys();
			Collections.sort(triSet.tris);
		}
		timer.stop(0);

		State bestState = null;
		timer.start(1);
		for (int turn = 0;; ++turn) {
			State curState;
			if (turn != 0) triSet.shuffle(rnd);

			if (N * 4.5 < P) {
				while (true) {
					curState = selectInitialState(triSet, Integer.MAX_VALUE);
					boolean ok = true;
					OUT: for (int i = 0; i < curState.poly.size(); ++i) {
						for (int j = i + 1; j < curState.poly.size(); ++j) {
							if (cross(curState.poly.get(i), curState.poly.get(j))) {
								ok = false;
								break OUT;
							}
						}
					}
					if (ok) break;
				}
			} else {
				curState = selectInitialState2(triSet);
			}

			ArrayList<Integer> useQ = new ArrayList<>();
			for (int i = 0; i < P; ++i) {
				if (curState.used.get(ps[i].id)) continue;
				int minDist = Integer.MAX_VALUE;
				for (Polygon poly : curState.poly) {
					for (Point pnt : poly.v) {
						minDist = Math.min(minDist, dist2(ps[i], pnt));
					}
				}
				useQ.add((minDist << 11) + i);
			}
			Collections.sort(useQ);
			for (int i = 0; i < useQ.size(); ++i) {
				useQ.set(i, useQ.get(i) & 0x7FF);
			}

			boolean complete = true;
			int pushBackCnt = 0;
			for (int pos = 0; pos < useQ.size(); ++pos) {
				if (pushBackCnt > useQ.size() - pos) {
					complete = false;
					break;
				}
				Point curP = ps[useQ.get(pos)];
				Append bestMove = null;
				for (int i = 0; i < curState.poly.size(); ++i) {
					Polygon poly = curState.poly.get(i);
					final int n = poly.v.size();
					for (int pi = 0; pi < n; ++pi) {
						final int ni = pi == n - 1 ? 0 : pi + 1;
						final Point ep1 = poly.v.get(pi);
						final Point ep2 = poly.v.get(ni);
						if (!triSet.exist[ep1.id][curP.id].get(ep2.id)) continue;
						final int val = triarea(ep1, curP, ep2);
						if (bestMove != null && curState.val + val >= bestMove.st.val + bestMove.diff) continue;
						if (cross(curState, poly, pi, curP)) continue;
						bestMove = new Append(curState, val, curP, i, ni);
					}
				}
				if (bestMove == null) {
					useQ.add(useQ.get(pos));
					++pushBackCnt;
					continue;
				}
				pushBackCnt = 0;
				curState = bestMove.apply();
			}

			if (complete) {
				bestScore = curState.val;
				bestState = curState;
				debug("initial result:" + bestScore + " turn:" + turn);
				break;
			}
		}
		timer.stop(1);
		timer.start(2);
		globalImprove(bestState, timelimit);
		timer.stop(2);
		if (bestState.val < bestScore) {
			bestScore = bestState.val;
			debug("improved area:" + bestState.val);
		}
		bestAns.clear();
		for (Polygon bestPoly : bestState.poly) {
			bestAns.add(bestPoly.v);
		}
	}

	TriangleSet enumeratePolys() {
		TriangleSet set = new TriangleSet(P);
		int maxDist = P < 400 ? 2000 : P <= 600 ? 1700 : 1700;
		maxDist *= maxDist;
		for (int i = 0; i < P; ++i) {
			Point pnt1 = ps[i];
			ArrayList<Angle> angles = new ArrayList<>();
			for (int j = i + 1; j < P; ++j) {
				final int d = dist2(pnt1, ps[j]);
				if (d < maxDist) {
					angles.add(new Angle(j, Math.atan2(ps[j].y - ps[i].y, ps[j].x - ps[i].x), d));
				}
			}
			Collections.sort(angles);
			for (int j = 0; j < angles.size(); ++j) {
				Point pnt2 = ps[angles.get(j).pi];
				if (j > 0 && triarea(pnt1, ps[angles.get(j - 1).pi], pnt2) == 0) continue;
				Point prev = null;
				int k = j + 1;
				for (; k < angles.size(); ++k) {
					if (triarea(pnt1, pnt2, ps[angles.get(k).pi]) != 0) {
						prev = ps[angles.get(k).pi];
						set.add(pnt1, pnt2, prev);
						break;
					}
				}
				for (++k; k < angles.size(); ++k) {
					Point pnt3 = ps[angles.get(k).pi];
					if (triarea(pnt2, prev, pnt3) <= 0) continue;
					prev = pnt3;
					set.add(pnt1, pnt2, pnt3);
				}
			}
		}
		debug("tri count:" + set.tris.size());
		return set;
	}

	State selectInitialState(TriangleSet triSet, int cutoff) {
		State initialState = new State(P);
		int count = P;
		int[] cand = new int[P];
		double DIST_TH = 400.0 / P;
		boolean fallback = false;
		final int LOOP = 10;
		int trisPos = 0;
		for (int i = 0; i < N; ++i) {
			int candPos = 0;
			for (int j = initialState.used.nextClearBit(0); j < P; j = initialState.used.nextClearBit(j + 1)) {
				cand[candPos++] = j;
			}
			ArrayList<Integer> bestPoly = new ArrayList<>();
			if (count < 8 || fallback) {
				for (; trisPos < triSet.tris.size(); ++trisPos) {
					Polygon tri = triSet.tris.get(trisPos);
					final int pi1 = tri.v.get(0).id;
					final int pi2 = tri.v.get(1).id;
					final int pi3 = tri.v.get(2).id;
					if (initialState.used.get(pi1) || initialState.used.get(pi2) || initialState.used.get(pi3)) continue;
					if (cross(initialState, tri)) continue;
					bestPoly.add(pi1);
					bestPoly.add(pi2);
					bestPoly.add(pi3);
					++trisPos;
					break;
				}
				if (bestPoly.isEmpty()) break;
				fallback = false;
			} else {
				final int MAX_V = 11;
				for (int j = 0; j < LOOP; ++j) {
					final int pip1 = rnd.nextInt(count);
					int pip2 = rnd.nextInt(count - 1);
					if (pip2 >= pip1) ++pip2;
					final Point p1 = i2p[cand[pip1]];
					final Point p2 = i2p[cand[pip2]];
					if (cross(initialState, p1, p2)) continue;
					double baseInv = 1.0 / Math.sqrt(dist2(p1, p2));
					ArrayList<Integer> curPoly = new ArrayList<>();
					for (int k = 0; k < count; ++k) {
						if (k == pip1 || k == pip2) continue;
						final int pi = cand[k];
						final Point p3 = i2p[pi];
						int area = Math.abs(triarea(p1, p2, p3));
						double dist = area * baseInv;
						if (dist > DIST_TH) continue;
						if (cross(initialState, p1, p3)) continue;
						curPoly.add(pi);
					}
					if (curPoly.size() > 0 && curPoly.size() <= MAX_V && curPoly.size() + 2 > bestPoly.size()) {
						bestPoly.clear();
						bestPoly.add(cand[pip1]);
						bestPoly.add(cand[pip2]);
						bestPoly.addAll(curPoly);
					}
				}
				if (bestPoly.isEmpty() || bestPoly.size() > MAX_V) {
					--i;
					fallback = true;
					continue;
				}
				determineBestOrder(bestPoly);
				if (bestPoly.isEmpty()) {
					--i;
					continue;
				}
			}

			Polygon poly = new Polygon(i2p[bestPoly.get(0)], i2p[bestPoly.get(1)], i2p[bestPoly.get(2)]);
			for (int j = 3; j < bestPoly.size(); ++j) {
				final int area = triarea(i2p[bestPoly.get(0)], i2p[bestPoly.get(j - 1)], i2p[bestPoly.get(j)]);
				poly = poly.add(i2p[bestPoly.get(j)], j, area);
			}
			initialState.add(poly);
			if (initialState.val >= cutoff) return initialState;
			count -= bestPoly.size();
		}
		return initialState;
	}

	int[] order = new int[20];
	boolean[] used = new boolean[20];
	ArrayList<Integer> bestOrder = new ArrayList<>();
	int bestOrderArea = Integer.MAX_VALUE;

	void determineBestOrder(ArrayList<Integer> ps) {
		bestOrder.clear();
		bestOrderArea = Integer.MAX_VALUE;
		order[0] = ps.get(0);
		used[0] = true;
		determineBestOrderRec(ps, 1, 0);
		ps.clear();
		if (bestOrderArea > 0) ps.addAll(bestOrder);
	}

	void determineBestOrderRec(ArrayList<Integer> ps, int pos, int area) {
		if (pos == ps.size()) {
			if (area < 0 || area >= bestOrderArea) return;
			for (int j = 1; j < pos - 2; ++j) {
				if (cross(i2p[order[0]], i2p[order[pos - 1]], i2p[order[j]], i2p[order[j + 1]])) return;
			}
			bestOrderArea = area;
			bestOrder.clear();
			for (int j = 0; j < ps.size(); ++j) {
				bestOrder.add(order[j]);
			}
			return;
		}
		for (int i = 1; i < ps.size(); ++i) {
			if (used[i]) continue;
			for (int j = 0; j < pos - 2; ++j) {
				if (cross(i2p[order[pos - 1]], i2p[ps.get(i)], i2p[order[j]], i2p[order[j + 1]])) return;
			}
			final int curArea = triarea(i2p[order[0]], i2p[order[pos - 1]], i2p[ps.get(i)]);
			order[pos] = ps.get(i);
			used[i] = true;
			determineBestOrderRec(ps, pos + 1, area + curArea);
			used[i] = false;
		}
	}

	State selectInitialState2(TriangleSet triSet) {
		State initialState = new State(P);
		for (int i = 0; i < triSet.tris.size(); ++i) {
			Polygon poly = triSet.tris.get(i);
			if (initialState.used.get(poly.v.get(0).id)) continue;
			if (initialState.used.get(poly.v.get(1).id)) continue;
			if (initialState.used.get(poly.v.get(2).id)) continue;
			if (cross(initialState, poly)) continue;
			initialState.add(poly);
			if (initialState.poly.size() == N) break;
			if (initialState.val + poly.area >= bestScore) break;
		}
		return initialState;
	}

	void globalImprove(State st, final long timelimit) {
		final int n = st.poly.size();
		int[] pi = new int[P];
		int[] next = new int[P];
		int[] prev = new int[P];
		int[] cnt = new int[n];
		int[] pa = new int[n];
		int[] edgeArea = new int[P];
		for (int i = 0; i < n; ++i) {
			final Polygon poly = st.poly.get(i);
			cnt[i] = poly.v.size();
			pa[i] = poly.area;
			for (int j = 0; j < poly.v.size(); ++j) {
				final Point p1 = poly.v.get(j);
				final Point p2 = poly.v.get(j == poly.v.size() - 1 ? 0 : j + 1);
				pi[p1.id] = i;
				next[p1.id] = p2.id;
				prev[p2.id] = p1.id;
			}
		}
		for (int i = 0; i < P; ++i) {
			final Point p1 = i2p[i];
			final Point p2 = i2p[next[p1.id]];
			final Point p3 = i2p[next[p2.id]];
			edgeArea[i] = triarea(p1, p3, p2);
		}

		double HEAT = initialHeat;
		int op1 = 0;
		int curArea = st.val;
		int bestArea = curArea;
		int[] bestNext = next.clone();
		int UPDATE_HEAT = 500000000 / (P + 100);
		int coolTurn = UPDATE_HEAT;
		int lastBestTurn = 0;
		debug("HEAT:" + HEAT);
		OUT: for (int turn = 1;; ++turn) {
			if ((turn & 0xFFFF) == 0) {
				final long elapsed = System.currentTimeMillis() - startTime;
				if (elapsed > timelimit) {
					debug("turn:" + turn);
					break;
				}
			}
			if (turn == coolTurn) {
				HEAT *= heatMul;
				coolTurn = turn + UPDATE_HEAT;
				debug("HEAT:" + HEAT + " bestArea:" + bestArea + " turn:" + turn);
			}
			if (turn > lastBestTurn + 3 * UPDATE_HEAT && HEAT * 8 < initialHeat) {
				HEAT *= 4;
				lastBestTurn = turn;
				debug("increase HEAT:" + HEAT);
			}
			op1 = op1 == P - 1 ? 0 : op1 + 1;
			//			counter.add(0);
			if (cnt[pi[op1]] == 3) continue;
			int areaAdd = edgeArea[op1];
			if (-areaAdd >= pa[pi[op1]]) continue;
			//			counter.add(1);
			final int op2 = next[op1];
			final int op3 = next[op2];
			final Point p1 = i2p[op1];
			final Point p2 = i2p[op2];
			int mpi1;
			if (areaAdd < 0) {
				mpi1 = rnd.nextInt(P);
				while (mpi1 == op1 || mpi1 == op2) {
					mpi1 = rnd.nextInt(P);
				}
			} else {
				int forward = rnd.nextInt(cnt[pi[op1]] - 2);
				if ((forward & 1) == 0) {
					forward /= 2;
					mpi1 = op3;
					for (int i = 0; i < forward; ++i) {
						mpi1 = next[mpi1];
					}
				} else {
					forward /= 2;
					mpi1 = prev[op1];
					for (int i = 0; i < forward; ++i) {
						mpi1 = prev[mpi1];
					}
				}
			}
			final int mpi2 = next[mpi1];
			final Point mp1 = i2p[mpi1];
			final Point mp2 = i2p[mpi2];
			final int areaRemove = triarea(mp1, p2, mp2);
			if (areaAdd * Integer.signum(areaRemove) >= 0) continue;
			//			counter.add(2);
			if (!transit(areaAdd + areaRemove, HEAT)) continue;

			if (pi[op2] == pi[mpi1]) {
				//				counter.add(3);
				// line to inside of polygon?
				if (mpi2 != op1 && mpi1 != op3) {
					final Point mp0 = i2p[prev[mpi1]];
					boolean inside = ccw(mp0, mp1, mp2) - ccw(mp0, mp1, p2) - ccw(p2, mp1, mp2) < 0;
					if (areaAdd > 0 ^ inside) continue;

					final Point mp3 = i2p[next[mpi2]];
					inside = ccw(mp1, mp2, mp3) - ccw(mp1, mp2, p2) - ccw(p2, mp2, mp3) < 0;
					if (areaAdd > 0 ^ inside) continue;
				}

				if (areaAdd < 0) {
					// new segment (p1-p3) crosses with polygon? 
					if (!triSet.exist[mpi1][op2].get(mpi2)) continue OUT;
					if (!triSet.exist[op1][op2].get(op3)) continue OUT;

					// new segments (p2-mp1), (p2-mp2) cross with polygon? 
					for (int i = 0; i < P; ++i) {
						if (i == op1 || i == op2) continue;
						final int ni = next[i];
						if (i != mpi2 && ni != mpi2) {
							if (cross(p2, mp2, i2p[i], i2p[ni])) continue OUT;
						}
						if (i != mpi1 && ni != mpi1) {
							if (cross(p2, mp1, i2p[i], i2p[ni])) continue OUT;
						}
					}
				} else {
					// new segment (p1-p3) crosses with polygon? 
					if (!triSet.exist[op1][op3].get(op2)) continue OUT;

					// new segments (p2-mp1), (p2-mp2) cross with polygon? 
					// sufficient to check current polygon
					for (int i = op3; i != op1; i = next[i]) {
						final int ni = next[i];
						if (i != mpi2 && ni != mpi2) {
							if (cross(p2, mp2, i2p[i], i2p[ni])) continue OUT;
						}
						if (i != mpi1 && ni != mpi1) {
							if (cross(p2, mp1, i2p[i], i2p[ni])) continue OUT;
						}
					}
				}
				//				counter.add(5);
			} else {
				//				counter.add(6);
				// new segment (p1-p3) crosses with polygon? 
				if (!triSet.exist[mpi1][op2].get(mpi2)) continue OUT;
				if (!triSet.exist[op1][op2].get(op3)) continue OUT;

				// new segments (p2-mp1), (p2-mp2) cross with polygon? 
				for (int i = 0; i < P; ++i) {
					if (i == op1 || i == op2) continue;
					final int ni = next[i];
					if (i != mpi2 && ni != mpi2) {
						if (cross(p2, mp2, i2p[i], i2p[ni])) continue OUT;
					}
					if (i != mpi1 && ni != mpi1) {
						if (cross(p2, mp1, i2p[i], i2p[ni])) continue OUT;
					}
				}
				//				counter.add(7);

				// avoid zero area polygon
				if (pa[pi[op1]] + areaAdd == 0) continue OUT;
			}

			//			counter.add(8);

			// new segments cross each other? 
			Point p3 = i2p[op3];
			if ((op3 != mpi1 && cross(mp1, p2, p1, p3)) || (op1 != mpi2 && cross(mp2, p2, p1, p3))) continue;
			//			counter.add(9);

			next[op1] = op3;
			next[mpi1] = op2;
			next[op2] = mpi2;
			prev[op2] = mpi1;
			prev[mpi2] = op2;
			prev[op3] = op1;
			cnt[pi[op2]]--;
			pi[op2] = pi[mpi2];
			cnt[pi[op2]]++;
			curArea += areaAdd + areaRemove;
			pa[pi[op1]] += areaAdd;
			pa[pi[op2]] += areaRemove;
			final int op0 = prev[op1];
			final int mpi0 = prev[mpi1];
			edgeArea[op0] = triarea(i2p[op0], p3, p1);
			edgeArea[op1] = triarea(p1, i2p[next[op3]], p3);
			edgeArea[op2] = triarea(p2, i2p[next[mpi2]], mp2);
			edgeArea[mpi0] = triarea(i2p[mpi0], p2, mp1);
			edgeArea[mpi1] = -areaRemove;

			if (curArea < bestArea) {
				bestArea = curArea;
				//				debug("bestArea:" + bestArea + " turn:" + turn);
				coolTurn = turn + P * P;
				lastBestTurn = turn;
				System.arraycopy(next, 0, bestNext, 0, P);
			}
		}

		st.val = 0;
		st.poly.clear();
		st.used.clear();
		for (int j = 0; j < P; ++j) {
			if (st.used.get(j)) continue;
			int cur = j;
			Polygon poly = new Polygon();
			while (true) {
				poly.v.add(i2p[cur]);
				cur = bestNext[cur];
				if (cur == j) break;
			}
			poly.area = calcArea(poly.v);
			st.add(poly);
		}
	}

	void globalImproveWithoutExchange(State st, final long timelimit) {
		final int n = st.poly.size();
		int[] pi = new int[P];
		int[] next = new int[P];
		int[] prev = new int[P];
		int[] cnt = new int[n];
		int[] pa = new int[n];
		int[] edgeArea = new int[P];
		int[][] polyIds = new int[n][];
		for (int i = 0; i < n; ++i) {
			final Polygon poly = st.poly.get(i);
			cnt[i] = poly.v.size();
			pa[i] = poly.area;
			polyIds[i] = new int[cnt[i]];
			for (int j = 0; j < poly.v.size(); ++j) {
				final Point p1 = poly.v.get(j);
				final Point p2 = poly.v.get(j == poly.v.size() - 1 ? 0 : j + 1);
				pi[p1.id] = i;
				next[p1.id] = p2.id;
				prev[p2.id] = p1.id;
				polyIds[i][j] = p1.id;
			}
		}
		for (int i = 0; i < P; ++i) {
			final Point p1 = i2p[i];
			final Point p2 = i2p[next[p1.id]];
			final Point p3 = i2p[next[p2.id]];
			edgeArea[i] = triarea(p1, p3, p2);
		}

		final double INITIAL_HEAT = 900;//800000.0 / P;
		double HEAT = INITIAL_HEAT;
		int op1 = 0;
		int curArea = st.val;
		int bestArea = curArea;
		int[] bestNext = next.clone();
		int UPDATE_HEAT = 1200000000 / (P + 100);
		int coolTurn = UPDATE_HEAT;
		int lastBestTurn = 0;
		debug("HEAT:" + HEAT);
		OUT: for (int turn = 1;; ++turn) {
			if ((turn & 0xFFFF) == 0) {
				final long elapsed = System.currentTimeMillis() - startTime;
				if (elapsed > timelimit) {
					debug("turn:" + turn);
					break;
				}
			}
			if (turn == coolTurn) {
				HEAT *= 0.96;
				coolTurn = turn + UPDATE_HEAT;
				debug("HEAT:" + HEAT + " bestArea:" + bestArea + " turn:" + turn);
			}
			if (turn > lastBestTurn + 3 * UPDATE_HEAT && HEAT * 8 < INITIAL_HEAT) {
				HEAT *= 4;
				lastBestTurn = turn;
				debug("increase HEAT:" + HEAT + " bestArea:" + bestArea + " turn:" + turn);
			}
			op1 = op1 == P - 1 ? 0 : op1 + 1;
			//			counter.add(0);
			//			if (cnt[pi[op1]] == 3) continue;  // assume size > 3
			int areaAdd = edgeArea[op1];
			final int op2 = next[op1];
			final int op3 = next[op2];
			final Point p1 = i2p[op1];
			final Point p2 = i2p[op2];
			int mpi1 = polyIds[pi[op1]][rnd.nextInt(cnt[pi[op1]])];
			while (mpi1 == op1 || mpi1 == op2) {
				mpi1 = polyIds[pi[op1]][rnd.nextInt(cnt[pi[op1]])];
			}
			final int mpi2 = next[mpi1];
			final Point mp1 = i2p[mpi1];
			final Point mp2 = i2p[mpi2];
			final int areaRemove = triarea(mp1, p2, mp2);
			if (areaAdd * Integer.signum(areaRemove) >= 0) continue;
			//			counter.add(1);
			if (!transit(areaAdd + areaRemove, HEAT)) continue;

			//			counter.add(2);
			// line to inside of polygon?
			if (mpi2 != op1 && mpi1 != op3) {
				final Point mp0 = i2p[prev[mpi1]];
				boolean inside = ccw(mp0, mp1, mp2) - ccw(mp0, mp1, p2) - ccw(p2, mp1, mp2) < 0;
				if (areaAdd > 0 ^ inside) continue;

				final Point mp3 = i2p[next[mpi2]];
				inside = ccw(mp1, mp2, mp3) - ccw(mp1, mp2, p2) - ccw(p2, mp2, mp3) < 0;
				if (areaAdd > 0 ^ inside) continue;
			}
			//			counter.add(3);

			// new segment (p2-mp2) cross with polygon? 
			if (mpi1 != op3) {
				for (int cp1 = op3;;) {
					final int cp2 = next[cp1];
					if (cross(p2, mp2, i2p[cp1], i2p[cp2])) {
						continue OUT;
					}
					if (cp2 == mpi1) break;
					cp1 = cp2;
				}
			}
			//			counter.add(4);
			if (mpi2 != op1) {
				for (int cp2 = op1;;) {
					final int cp1 = prev[cp2];
					if (cp1 == mpi2) break;
					if (cross(p2, mp2, i2p[cp1], i2p[cp2])) {
						continue OUT;
					}
					cp2 = cp1;
				}
			}
			//			counter.add(5);

			// new segment (p1-p3) crosses with polygon? 
			Point p3 = i2p[op3];
			for (int i = next[op3];; i = next[i]) {
				final int ni = next[i];
				if (ni == op1) break;
				if (cross(p1, p3, i2p[i], i2p[ni])) continue OUT;
			}
			//			counter.add(6);

			// new segment (p2-mp1) cross with polygon? 
			if (mpi1 != op3) {
				for (int cp1 = op3;;) {
					final int cp2 = next[cp1];
					if (cp2 == mpi1) break;
					if (cross(p2, mp1, i2p[cp1], i2p[cp2])) {
						continue OUT;
					}
					cp1 = cp2;
				}
			}
			//			counter.add(7);
			if (mpi2 != op1) {
				for (int cp2 = op1;;) {
					final int cp1 = prev[cp2];
					if (cross(p2, mp1, i2p[cp1], i2p[cp2])) {
						continue OUT;
					}
					if (cp1 == mpi2) break;
					cp2 = cp1;
				}
			}
			//			counter.add(8);

			// new segments cross each other? 
			if ((op3 != mpi1 && cross(mp1, p2, p1, p3)) || (op1 != mpi2 && cross(mp2, p2, p1, p3))) continue;

			if (-areaAdd >= pa[pi[op1]]) continue;
			//			counter.add(10);

			next[op1] = op3;
			next[mpi1] = op2;
			next[op2] = mpi2;
			prev[op2] = mpi1;
			prev[mpi2] = op2;
			prev[op3] = op1;
			curArea += areaAdd + areaRemove;
			pa[pi[op1]] += areaAdd + areaRemove;
			final int op0 = prev[op1];
			final int mpi0 = prev[mpi1];
			edgeArea[op0] = triarea(i2p[op0], p3, p1);
			edgeArea[op1] = triarea(p1, i2p[next[op3]], p3);
			edgeArea[op2] = triarea(p2, i2p[next[mpi2]], mp2);
			edgeArea[mpi0] = triarea(i2p[mpi0], p2, mp1);
			edgeArea[mpi1] = -areaRemove;

			if (curArea < bestArea) {
				bestArea = curArea;
				//				debug("bestArea:" + bestArea + " turn:" + turn);
				coolTurn = turn + UPDATE_HEAT / 4;
				lastBestTurn = turn;
				System.arraycopy(next, 0, bestNext, 0, P);
			}
		}

		st.val = 0;
		st.poly.clear();
		st.used.clear();
		for (int j = 0; j < P; ++j) {
			if (st.used.get(j)) continue;
			int cur = j;
			Polygon poly = new Polygon();
			while (true) {
				poly.v.add(i2p[cur]);
				cur = bestNext[cur];
				if (cur == j) break;
			}
			poly.area = calcArea(poly.v);
			st.add(poly);
		}
	}

	static final class TriangleSet {
		ArrayList<Polygon> tris;
		BitSet[][] exist;

		TriangleSet(int P) {
			this.tris = new ArrayList<>(P * P * 2);
			this.exist = new BitSet[P][P];
			for (int i = 0; i < P; ++i) {
				for (int j = 0; j < P; ++j) {
					this.exist[i][j] = new BitSet(P);
				}
			}
		}

		void add(Point p1, Point p2, Point p3) {
			Polygon poly = new Polygon(p1, p2, p3);
			tris.add(poly);
			exist[p1.id][p2.id].set(p3.id);
			exist[p2.id][p3.id].set(p1.id);
			exist[p3.id][p1.id].set(p2.id);
		}

		void shuffle(XorShift rnd) {
			for (int i = 0; i < Math.min(1000, tris.size()); ++i) {
				int ch1 = rnd.nextInt(100);
				if (ch1 + i >= tris.size()) continue;
				Polygon tmp = tris.get(i);
				tris.set(i, tris.get(ch1 + i));
				tris.set(ch1 + i, tmp);
			}
		}
	}

	static final class Angle implements Comparable<Angle> {
		int pi, dist;
		double theta;

		Angle(int pi, double theta, int d) {
			this.pi = pi;
			this.theta = theta;
			this.dist = d;
		}

		public int compareTo(Angle o) {
			if (Math.abs(this.theta - o.theta) > 1e-8) return Double.compare(this.theta, o.theta);
			return Integer.compare(this.dist, o.dist);
		}
	}

	static final class Polygon implements Comparable<Polygon> {
		ArrayList<Point> v;
		int area;

		Polygon() {
			this.v = new ArrayList<>();
		}

		Polygon(Point p1, Point p2, Point p3) {
			this.v = new ArrayList<>(3);
			v.add(p1);
			v.add(p2);
			v.add(p3);
			area = triarea(p1, p2, p3);
		}

		Polygon(ArrayList<Point> ps) {
			this.v = new ArrayList<>(ps);
			this.area = calcArea(ps);
		}

		Polygon add(Point p, int pos, int areaDiff) {
			final int n = this.v.size();
			Polygon ret = new Polygon();
			ret.area = this.area;
			for (int i = 0; i < pos; ++i) {
				ret.v.add(this.v.get(i));
			}
			ret.v.add(p);
			for (int i = pos; i < n; ++i) {
				ret.v.add(this.v.get(i));
			}
			ret.area += areaDiff;
			return ret;
		}

		public int compareTo(Polygon o) {
			return Integer.compare(this.area, o.area);
		}
	}

	static final class State implements Comparable<State> {
		final ArrayList<Polygon> poly = new ArrayList<>();
		int val;
		BitSet used;

		State(int P) {
			this.val = 0;
			this.used = new BitSet(P);
		}

		State(State o) {
			this.poly.addAll(o.poly);
			this.used = (BitSet) o.used.clone();
			this.val = o.val;
		}

		void add(Polygon p) {
			this.poly.add(p);
			this.val += p.area;
			for (Point pnt : p.v) {
				used.set(pnt.id);
			}
		}

		public int compareTo(State o) {
			return Integer.compare(this.val, o.val);
		}
	}

	static final class Append implements Comparable<Append> {
		State st;
		int diff;
		Point pnt;
		int polyIdx, edgeIdx;

		Append(State st, int diff, Point pnt, int pi, int ei) {
			this.st = st;
			this.diff = diff;
			this.pnt = pnt;
			this.polyIdx = pi;
			this.edgeIdx = ei;
		}

		State apply() {
			State ret = new State(this.st);
			ret.val += this.diff;
			Polygon np = ret.poly.get(this.polyIdx).add(this.pnt, this.edgeIdx, this.diff);
			ret.poly.set(this.polyIdx, np);
			return ret;
		}

		public int compareTo(Append o) {
			return Integer.compare(this.st.val + this.diff, o.st.val + o.diff);
		}
	}

	boolean cross(State st, Polygon append, int appendPos, Point pnt) {
		final int np = appendPos == append.v.size() - 1 ? 0 : appendPos + 1;
		Point ep1 = append.v.get(appendPos);
		Point ep2 = append.v.get(np);
		for (Polygon p : st.poly) {
			if (p == append) {
				for (int i = 0; i < p.v.size(); ++i) {
					int ni = i == p.v.size() - 1 ? 0 : i + 1;
					if (i != appendPos && ni != appendPos) {
						if (cross(p.v.get(i), p.v.get(ni), ep1, pnt)) return true;
					}
					if (i != np && ni != np) {
						if (cross(p.v.get(i), p.v.get(ni), ep2, pnt)) return true;
					}
				}
			} else {
				if (cross(p, ep1, pnt)) return true;
				if (cross(p, ep2, pnt)) return true;
			}
		}
		return false;
	}

	boolean cross(State st, Polygon poly) {
		for (Polygon p : st.poly) {
			if (cross(p, poly)) return true;
		}
		return false;
	}

	boolean cross(State st, Point p1, Point p2) {
		for (Polygon p : st.poly) {
			if (cross(p, p1, p2)) return true;
		}
		return false;
	}

	boolean cross(Polygon poly1, Polygon poly2) {
		for (int i = 0; i < poly2.v.size(); ++i) {
			Point p1 = poly2.v.get(i);
			Point p2 = poly2.v.get(i == poly2.v.size() - 1 ? 0 : i + 1);
			if (cross(poly1, p1, p2)) return true;
		}
		return false;
	}

	boolean cross(Polygon poly, Point p1, Point p2) {
		for (int i = 0; i < poly.v.size(); ++i) {
			Point p3 = poly.v.get(i);
			Point p4 = poly.v.get(i == poly.v.size() - 1 ? 0 : i + 1);
			if (cross(p1, p2, p3, p4)) return true;
		}
		return false;
	}

	void solveVoronoi(long timelimit) {
		final long TIME_FINAL_IMPROVE = timelimit * 5 / 10;
		long loopStartTime = System.currentTimeMillis();
		for (int turn = 0;; ++turn) {
			if (loopStartTime - startTime + worstTime > timelimit - TIME_FINAL_IMPROVE) {
				debug("turn:" + turn + " worstTime:" + worstTime);
				break;
			}
			timer.start(10);
			ArrayList<ArrayList<Point>> cell;
			cell = dividePoints();
			timer.stop(10);
			int sumArea = 0;
			ArrayList<ArrayList<Point>> curAns = new ArrayList<>();
			for (int i = 0; i < cell.size() && sumArea < bestScore; ++i) {
				curAns.add(new ArrayList<>());
				int curArea = area(cell.get(i), curAns.get(i), turn == 0);
				if (curArea == 0) { // invalid
					sumArea = Integer.MAX_VALUE;
					break;
				}
				sumArea += curArea;
			}
			if (sumArea < bestScore) {
				bestScore = sumArea;
				bestAns = curAns;
				debug("bestScore:" + bestScore + " turn:" + turn);
				if (turn != 0) break;
			}
			long curTime = System.currentTimeMillis();
			worstTime = Math.max(worstTime, curTime - loopStartTime);
			loopStartTime = curTime;
		}

		if (P > 175 * N - 250) {
			State bestState = new State(P);
			for (int i = 0; i < bestAns.size(); ++i) {
				Polygon poly = new Polygon(bestAns.get(i));
				bestState.add(poly);
			}
			globalImproveWithoutExchange(bestState, timelimit);
			if (bestState.val < bestScore) {
				bestScore = bestState.val;
				debug("last area:" + bestState.val);
			}
			bestAns.clear();
			for (Polygon bestPoly : bestState.poly) {
				bestAns.add(bestPoly.v);
			}
		} else {
			long worstImproveTime = 0;
			long improveStartTime = System.currentTimeMillis();
			double heatAmp = 8;
			for (int turn = 0;; ++turn) {
				if (improveStartTime - startTime + worstImproveTime > timelimit) {
					debug("improve turn:" + turn);
					debug("worst improve time:" + worstImproveTime);
					break;
				}
				ArrayList<Point> ba = bestAns.get(turn % bestAns.size());
				final int area = calcArea(ba);
				final int newArea = improve(ba, area, heatAmp);
				//				debug(ba.size() + " " + area + "->" + newArea);
				if (newArea < area) {
					bestScore += newArea - area;
					debug("bestArea:" + bestScore + " turn:" + turn);
				}
				long improveEndTime = System.currentTimeMillis();
				worstImproveTime = Math.max(worstImproveTime, improveEndTime - improveStartTime);
				improveStartTime = improveEndTime;
				if (turn % bestAns.size() == 0) {
					heatAmp *= 0.9;
					if (heatAmp < 1) heatAmp = 5;
					debug("heatAmp:" + heatAmp);
				}
			}
		}
	}

	ArrayList<ArrayList<Point>> dividePoints() {
		int[] centerX = new int[N];
		int[] centerY = new int[N];
		int[] sumX = new int[N];
		int[] sumY = new int[N];
		int[] cnt = new int[N];
		int[] belong = new int[P];
		for (int i = 0; i < N; ++i) {
			int pi = rnd.nextInt(P);
			centerX[i] = ps[pi].x;
			centerY[i] = ps[pi].y;
		}
		for (int i = 0; i < N; ++i) {
			Arrays.fill(sumX, 0);
			Arrays.fill(sumY, 0);
			Arrays.fill(cnt, 0);
			boolean update = false;
			for (int j = 0; j < P; ++j) {
				int minD = Integer.MAX_VALUE;
				int minI = 0;
				for (int k = 0; k < N; ++k) {
					int d = sq(ps[j].x - centerX[k]) + sq(ps[j].y - centerY[k]);
					if (d < minD) {
						minD = d;
						minI = k;
					}
				}
				sumX[minI] += ps[j].x;
				sumY[minI] += ps[j].y;
				cnt[minI]++;
				if (belong[j] != minI) {
					belong[j] = minI;
					update = true;
				}
			}
			for (int j = 0; j < N; ++j) {
				if (cnt[j] > 0) {
					centerX[j] = (sumX[j] + cnt[j] / 2) / cnt[j];
					centerY[j] = (sumY[j] + cnt[j] / 2) / cnt[j];
				} else {
					centerX[j] = rnd.nextInt(701);
					centerY[j] = rnd.nextInt(701);
				}
			}
			if (!update) {
				break;
			}
		}
		ArrayList<ArrayList<Point>> cell = new ArrayList<>();
		for (int i = 0; i < N; ++i) {
			cell.add(new ArrayList<>());
		}
		for (int i = 0; i < P; ++i) {
			if (cnt[belong[i]] <= 3) {
				int minD = Integer.MAX_VALUE;
				int minI = 0;
				for (int j = 0; j < N; ++j) {
					if (cnt[j] <= 3) continue;
					int d = sq(ps[i].x - centerX[j]) + sq(ps[i].y - centerY[j]);
					if (d < minD) {
						minD = d;
						minI = j;
					}
				}
				belong[i] = minI;
				cnt[minI]++;
			}
		}
		for (int i = 0; i < P; ++i) {
			cell.get(belong[i]).add(ps[i]);
		}
		for (int i = 0; i < cell.size(); ++i) {
			if (cell.get(i).isEmpty()) {
				cell.remove(i);
				--i;
			}
		}
		return cell;
	}

	int area(ArrayList<Point> ps, ArrayList<Point> ret, boolean safe) {
		// create convex
		timer.start(11);
		for (int i = 0; i < ps.size(); ++i) {
			ps.get(i).id |= (i << 16);
		}
		final int n = ps.size();
		boolean[] used = new boolean[n];
		ArrayList<Point> lower = new ArrayList<>();
		for (int i = 0; i < n; ++i) {
			while (lower.size() >= 2 && ccw(lower.get(lower.size() - 2), lower.get(lower.size() - 1), ps.get(i)) < 0) {
				lower.remove(lower.size() - 1);
			}
			lower.add(ps.get(i));
		}
		for (Point p : lower) {
			used[p.id >> 16] = true;
		}

		ArrayList<Point> upper = new ArrayList<>();
		for (int i = n - 1; i >= 0; --i) {
			if (i != n - 1 && i != 0 && used[i]) continue;
			while (upper.size() >= 2 && ccw(upper.get(upper.size() - 2), upper.get(upper.size() - 1), ps.get(i)) < 0) {
				upper.remove(upper.size() - 1);
			}
			upper.add(ps.get(i));
		}
		for (Point p : upper) {
			used[p.id >> 16] = true;
		}
		boolean convex = n == upper.size() + lower.size() - 2;
		for (int i = 0; i < n; ++i) {
			ps.get(i).id &= 0xFFFF;
		}
		timer.stop(11);

		timer.start(12);
		if (!safe) {
			ret.addAll(lower);
			for (int i = 1; i < upper.size() - 1; ++i) {
				ret.add(upper.get(i));
			}
			ArrayList<Point> inner = new ArrayList<>();
			for (int i = 0; i < n; ++i) {
				if (!used[i]) inner.add(ps.get(i));
			}
			for (int i = 0; i < inner.size(); ++i) {
				int pos = i + rnd.nextInt(inner.size() - i);
				Point tmp = inner.get(i);
				inner.set(i, inner.get(pos));
				inner.set(pos, tmp);
			}
			int seqInvalid = 0;
			for (int pos = 0; pos < inner.size(); ++pos) {
				if (seqInvalid >= inner.size() - pos) return 0;
				Point in = inner.get(pos);
				final int m = ret.size();
				int maxArea = Integer.MIN_VALUE;
				int maxIdx = -1;
				OUT: for (int i = 0; i < m; ++i) {
					final int ni = i == m - 1 ? 0 : i + 1;
					Point p1 = ret.get(i);
					Point p2 = ret.get(ni);
					int area = triarea(p1, p2, in);
					if (area <= maxArea) continue;
					for (int j = ni; j != i;) {
						final int nj = j == m - 1 ? 0 : j + 1;
						if (j != ni) {
							if (cross(p2, in, ret.get(j), ret.get(nj))) {
								++i;
								continue OUT;
							}
						}
						if (nj != i) {
							if (cross(p1, in, ret.get(j), ret.get(nj))) continue OUT;
						}
						j = nj;
					}
					maxArea = area;
					maxIdx = i;
				}
				if (maxIdx == -1) {
					inner.add(in);
					++seqInvalid;
				} else {
					ret.add(maxIdx + 1, in);
					seqInvalid = 0;
				}
			}
		} else {
			int lowerIdx = 1;
			ret.add(lower.get(0));
			for (int i = 0; i < n; ++i) {
				if (used[i]) continue;
				while (ps.get(i).x >= lower.get(lowerIdx).x) {
					ret.add(lower.get(lowerIdx++));
				}
				ret.add(ps.get(i));
			}
			while (lowerIdx < lower.size()) {
				ret.add(lower.get(lowerIdx++));
			}
			for (int i = 1; i < upper.size() - 1; ++i) {
				ret.add(upper.get(i));
			}
		}
		int area = calcArea(ret);
		timer.stop(12);
		if (area == 0) return 0;
		timer.start(13);
		if (!convex && !safe) {
			//			area = improve(ret, area);
		}
		timer.stop(13);
		return area;
	}

	int improve2(ArrayList<Point> ps, int curArea) {
		final int n = ps.size();
		final int improveCount = Math.min(30000, n * 20);
		int op1 = 0;
		double HEAT = 490000 / (Math.PI * P);
		int bestTurn = 0;
		int bestArea = curArea;
		OUT: for (int i = 0; i < improveCount; ++i) {
			if (i > bestTurn + n) {
				HEAT *= 0.5;
				bestTurn = i;
			}
			if (i == improveCount - n * n) {
				HEAT = 0;
			}
			op1 = op1 == n - 1 ? 0 : op1 + 1;
			final int op2 = op1 == n - 1 ? 0 : op1 + 1;
			final int op3 = op2 == n - 1 ? 0 : op2 + 1;
			Point p1 = ps.get(op1);
			Point p2 = ps.get(op2);
			Point p3 = ps.get(op3);
			int areaAdd = -triarea(p1, p2, p3);
			if (-areaAdd >= curArea || areaAdd == 0) continue;

			// connected segment (p1-p3) crosses with polygon? 
			for (int tp1 = (op3 == n - 1 ? 0 : op3 + 1);;) {
				final int tp2 = tp1 == n - 1 ? 0 : tp1 + 1;
				if (tp2 == op1) break;
				if (cross(p1, p3, ps.get(tp1), ps.get(tp2))) {
					continue OUT;
				}
				tp1 = tp2;
			}

			int areaRemove = Integer.MAX_VALUE;
			int insertPos = -1;
			if (areaAdd < 0) {
				// select min added area among visible segment from p2
				ArrayList<SegAngle> angles = new ArrayList<>();
				angles.add(new SegAngle(op1, true, p2, p1));
				angles.add(new SegAngle(op1, false, p2, p3));
				for (int segs = op3; segs != op1;) {
					final int sege = segs == n - 1 ? 0 : segs + 1;
					final Point sp1 = ps.get(segs);
					final Point sp2 = ps.get(sege);
					if (ccw(p2, sp1, sp2) < 0) {
						angles.add(new SegAngle(segs, true, p2, sp1));
						angles.add(new SegAngle(segs, false, p2, sp2));
					}
					segs = sege;
				}
				for (int j = 1; j < angles.size(); ++j) {
					if (angles.get(j).theta < angles.get(0).theta) {
						angles.get(j).theta += 2 * Math.PI;
					}
					angles.get(j).theta *= -1;
				}
				angles.get(0).theta *= -1;
				Collections.sort(angles);
				BitSet exist = new BitSet(n);
				for (SegAngle angle : angles) {
					if (angle.start == 1) {
						exist.set(angle.idx);
					} else {
						exist.clear(angle.idx);
					}
				}
				int startPos = -1;
				boolean dirty = false;
				for (int j = 0; j < angles.size(); ++j) {
					final SegAngle angle = angles.get(j);
					if (angle.start == 1) {
						if (startPos == -1) {
							// select nearest segment;
							startPos = angle.idx;
							double minDist = 1;
							for (int ci = exist.nextSetBit(0); ci >= 0; ci = exist.nextSetBit(ci + 1)) {
								final double d = dist(p2, ps.get(angle.idx), ps.get(ci), ps.get(ci == n - 1 ? 0 : ci + 1));
								if (d < minDist) {
									minDist = d;
									startPos = ci;
								}
							}
							dirty = startPos != angle.idx;
						} else {
							final int endPos = startPos == n - 1 ? 0 : startPos + 1;
							if (ccw(ps.get(startPos), ps.get(endPos), ps.get(angle.idx)) < 0) {
								startPos = angle.idx;
								dirty = false;
							}
						}
						exist.set(angle.idx);
					} else {
						if (angle.idx == startPos) {
							// end of current segment
							if (angle.idx != op1 && !dirty) {
								final int endPos = startPos == n - 1 ? 0 : startPos + 1;
								final int area = -triarea(p2, ps.get(startPos), ps.get(endPos));
								if (area < areaRemove) {
									areaRemove = area;
									insertPos = startPos;
								}
							}
							startPos = -1;
						}
						exist.clear(angle.idx);
					}
				}
				if (startPos != -1 && !dirty) {
					// consider last segment
					final int endPos = startPos == n - 1 ? 0 : startPos + 1;
					if (endPos == op1) {
						final int area = -triarea(p2, ps.get(startPos), ps.get(endPos));
						if (area < areaRemove) {
							areaRemove = area;
							insertPos = startPos;
						}
					}
				}
			} else {
				// select max removed area among visible segment from p2
				ArrayList<SegAngle> angles = new ArrayList<>();
				angles.add(new SegAngle(op1, true, p2, p1));
				angles.add(new SegAngle(op1, false, p2, p3));
				for (int segs = op3; segs != op1;) {
					final int sege = segs == n - 1 ? 0 : segs + 1;
					final Point sp1 = ps.get(segs);
					final Point sp2 = ps.get(sege);
					if (ccw(p2, sp1, sp2) > 0) {
						angles.add(new SegAngle(segs, true, p2, sp1));
						angles.add(new SegAngle(segs, false, p2, sp2));
					}
					segs = sege;
				}
				for (int j = 1; j < angles.size(); ++j) {
					if (angles.get(j).theta < angles.get(0).theta) {
						angles.get(j).theta += 2 * Math.PI;
					}
				}
				Collections.sort(angles);
				BitSet exist = new BitSet(n);
				for (SegAngle angle : angles) {
					if (angle.start == 1) {
						exist.set(angle.idx);
					} else {
						exist.clear(angle.idx);
					}
				}
				int startPos = -1;
				boolean dirty = false;
				for (int j = 0; j < angles.size(); ++j) {
					final SegAngle angle = angles.get(j);
					if (angle.start == 1) {
						if (startPos == -1) {
							// select nearest segment;
							startPos = angle.idx;
							double minDist = 1;
							for (int ci = exist.nextSetBit(0); ci >= 0; ci = exist.nextSetBit(ci + 1)) {
								final double d = dist(p2, ps.get(angle.idx), ps.get(ci), ps.get(ci == n - 1 ? 0 : ci + 1));
								if (d < minDist) {
									minDist = d;
									startPos = ci;
								}
							}
							dirty = startPos != angle.idx;
						} else {
							final int endPos = startPos == n - 1 ? 0 : startPos + 1;
							if (ccw(ps.get(startPos), ps.get(endPos), ps.get(angle.idx)) > 0) {
								startPos = angle.idx;
								dirty = false;
							}
						}
						exist.set(angle.idx);
					} else {
						if (angle.idx == startPos) {
							// end of current segment
							if (angle.idx != op1 && !dirty) {
								final int endPos = startPos == n - 1 ? 0 : startPos + 1;
								final int area = -triarea(p2, ps.get(startPos), ps.get(endPos));
								//								debug(op2 + " " + angle.idx + " " + area);
								if (area < areaRemove) {
									areaRemove = area;
									insertPos = startPos;
								}
							}
							startPos = -1;
						}
						exist.clear(angle.idx);
					}
				}
				if (startPos != -1 && !dirty) {
					// consider last segment
					final int endPos = startPos == n - 1 ? 0 : startPos + 1;
					if (endPos == op1) {
						final int area = -triarea(p2, ps.get(startPos), ps.get(endPos));
						if (area < areaRemove) {
							areaRemove = area;
							insertPos = startPos;
						}
					}
				}
			}
			if (insertPos == -1) continue;
			if (areaAdd + areaRemove > HEAT) continue;
			insertPos++;

			ps.remove(op2);
			ps.add(op2 < insertPos ? insertPos - 1 : insertPos, p2);
			curArea += areaAdd + areaRemove;
			if (curArea < bestArea) {
				bestArea = curArea;
				bestTurn = i;
			}

		}
		return curArea;
	}

	static double dist(Point from, Point to, Point p1, Point p2) {
		final int dx = p2.x - p1.x;
		final int dy = p2.y - p1.y;
		return 1.0 * (-from.x * dy + from.y * dx + p1.x * p2.y - p1.y * p2.x)
				/ (dy * (to.x - from.x) - dx * (to.y - from.y));
	}

	int improve(ArrayList<Point> ps, int curArea, double heatAmp) {
		final int n = ps.size();
		final int improveCount = Math.min(300000, n * n * 20);
		int op1 = 0;
		int op2 = 1;
		int op3 = 2;

		int UPDATE_HEAT = 2 * n * n;//10000;//2000000 / (P + 100);
		double HEAT = heatAmp * 490000 / (Math.PI * P);
		int coolTurn = UPDATE_HEAT;
		int bestArea = curArea;
		ArrayList<Point> bestPoints = new ArrayList<>(ps);
		OUT: for (int turn = 0; turn < improveCount; ++turn) {
			if (turn == coolTurn) {
				HEAT *= 0.9;
				coolTurn = turn + UPDATE_HEAT;
			}
			op1 = op2;
			op2 = op3;
			op3 = op3 == n - 1 ? 0 : op3 + 1;
			Point p1 = ps.get(op1);
			Point p2 = ps.get(op2);
			Point p3 = ps.get(op3);
			int areaAdd = -triarea(p1, p2, p3);
			//			counter.add(0);
			if (-areaAdd >= curArea) continue;
			//			counter.add(1);
			int mpi1 = rnd.nextInt(n);
			while (mpi1 == op1 || mpi1 == op2) {
				mpi1 = rnd.nextInt(n);
			}
			final int mpi2 = mpi1 == n - 1 ? 0 : mpi1 + 1;
			final Point mp1 = ps.get(mpi1);
			final Point mp2 = ps.get(mpi2);
			int areaRemove = triarea(mp1, p2, mp2);
			if (areaAdd * Integer.signum(areaRemove) >= 0) continue;
			//			counter.add(2);
			if (!transit(areaAdd + areaRemove, HEAT)) continue;
			//			counter.add(3);

			// line to inside of polygon?
			if (mpi2 != op1 && mpi1 != op3) {
				final Point mp0 = ps.get(mpi1 == 0 ? n - 1 : mpi1 - 1);
				boolean inside = ccw(mp0, mp1, mp2) - ccw(mp0, mp1, p2) - ccw(p2, mp1, mp2) < 0;
				if (areaAdd > 0 ^ inside) continue;

				final Point mp3 = ps.get(mpi2 == n - 1 ? 0 : mpi2 + 1);
				inside = ccw(mp1, mp2, mp3) - ccw(mp1, mp2, p2) - ccw(p2, mp2, mp3) < 0;
				if (areaAdd > 0 ^ inside) continue;
			}
			//			counter.add(4);

			// new segment (p2-mp2) cross with polygon? 
			if (mpi1 != op3) {
				for (int cp1 = op3;;) {
					final int cp2 = cp1 == n - 1 ? 0 : cp1 + 1;
					if (cp2 == mpi1) {
						if (cross(p2, mp2, ps.get(cp1), ps.get(cp2))) {
							continue OUT;
						}
						break;
					}
					if (cross(p2, mp2, ps.get(cp1), ps.get(cp2))) {
						continue OUT;
					}
					cp1 = cp2;
				}
			}
			//			counter.add(5);
			if (mpi2 != op1) {
				for (int cp2 = op1;;) {
					final int cp1 = cp2 == 0 ? n - 1 : cp2 - 1;
					if (cp1 == mpi2) {
						break;
					}
					if (cross(p2, mp2, ps.get(cp1), ps.get(cp2))) {
						continue OUT;
					}
					cp2 = cp1;
				}
			}
			//			counter.add(6);

			// new segment (p1-p3) crosses with polygon? 
			for (int tp1 = (op3 == n - 1 ? 0 : op3 + 1);;) {
				final int tp2 = tp1 == n - 1 ? 0 : tp1 + 1;
				if (tp2 == op1) break;
				if (cross(p1, p3, ps.get(tp1), ps.get(tp2))) {
					continue OUT;
				}
				tp1 = tp2;
			}
			//			counter.add(7);

			// new segment (p2-mp1) cross with polygon? 
			if (mpi1 != op3) {
				for (int cp1 = op3;;) {
					final int cp2 = cp1 == n - 1 ? 0 : cp1 + 1;
					if (cp2 == mpi1) {
						break;
					}
					if (cross(mp1, p2, ps.get(cp1), ps.get(cp2))) {
						continue OUT;
					}
					cp1 = cp2;
				}
			}
			//			counter.add(8);
			if (mpi2 != op1) {
				for (int cp2 = op1;;) {
					final int cp1 = cp2 == 0 ? n - 1 : cp2 - 1;
					if (cp1 == mpi2) {
						if (cross(mp1, p2, ps.get(cp1), ps.get(cp2))) {
							continue OUT;
						}
						break;
					}
					if (cross(mp1, p2, ps.get(cp1), ps.get(cp2))) {
						continue OUT;
					}
					cp2 = cp1;
				}
			}
			//			counter.add(9);

			if ((op3 != mpi1 && cross(mp1, p2, p1, p3)) || (op1 != mpi2 && cross(mp2, p2, p1, p3))) continue;
			//			counter.add(10);
			ps.remove(op2);
			ps.add(op2 < mpi2 ? mpi2 - 1 : mpi2, p2);
			curArea += areaAdd + areaRemove;
			if (curArea < bestArea) {
				bestArea = curArea;
				coolTurn = turn + 2 * n * n;
				bestPoints.clear();
				bestPoints.addAll(ps);
			}
		}
		//		if (curArea != bestArea) debug("diff:" + (curArea - bestArea) + " cur:" + curArea + " best:" + bestArea);
		ps.clear();
		ps.addAll(bestPoints);
		return bestArea;
	}

	boolean transit(int diff, double heat) {
		if (diff <= 0) return true;
		if (diff >= heat * 4) return false;
		return rnd.nextDouble() <= Math.exp(-2 * diff / heat);
		//		return rnd.nextDouble() * heat <= heat - diff;
	}

	static int calcArea(ArrayList<Point> ps) {
		final int n = ps.size();
		int area = 0;
		for (int i = 0; i < n; ++i) {
			Point p1 = ps.get(i);
			Point p2 = ps.get(i == n - 1 ? 0 : i + 1);
			area += (p1.y + p2.y) * (p2.x - p1.x);
		}
		return Math.abs(area);
	}

	static int triarea(Point a, Point b, Point c) {
		int dx1 = b.x - a.x;
		int dy1 = b.y - a.y;
		int dx2 = c.x - a.x;
		int dy2 = c.y - a.y;
		return dx1 * dy2 - dx2 * dy1;
	}

	static int ccw(Point a, Point b, Point c) {
		return Integer.signum(triarea(a, b, c));
	}

	static boolean cross(Point p1, Point p2, Point p3, Point p4) {
		return ccw(p1, p2, p3) * ccw(p1, p2, p4) <= 0 && ccw(p3, p4, p1) * ccw(p3, p4, p2) <= 0;
	}

	static int dist2(Point p1, Point p2) {
		return sq(p1.x - p2.x) + sq(p1.y - p2.y);
	}

	static int sq(int v) {
		return v * v;
	}

	static class SegAngle implements Comparable<SegAngle> {
		int idx;
		int start;
		double theta;
		int d;

		SegAngle(int idx, boolean start, Point from, Point to) {
			this.idx = idx;
			this.start = start ? 1 : -1;
			this.theta = Math.atan2(to.y - from.y, to.x - from.x);
			this.d = dist2(from, to);
		}

		public int compareTo(SegAngle o) {
			int ret = Double.compare(this.theta, o.theta);
			if (ret == 0) {
				if (this.start != o.start) {
					ret = -this.start;
				} else {
					ret = Integer.compare(this.d, o.d);
				}
			}
			return ret;
		}

		public String toString() {
			return String.format("(%d, %d, %.3f)", this.idx, this.start, this.theta);
		}
	}

	static final class Point implements Comparable<Point> {
		int x, y, id;

		Point(int x, int y, int id) {
			this.x = x;
			this.y = y;
			this.id = id;
		}

		public int compareTo(Point o) {
			if (this.x != o.x) return Integer.compare(this.x, o.x);
			return Integer.compare(this.y, o.y);
		}

		public String toString() {
			return "(" + this.x + "," + this.y + ")";
		}
	}

	static void debug(String str) {
		if (DEBUG) System.err.println(str);
	}

	static void debug(Object... obj) {
		if (DEBUG) System.err.println(Arrays.deepToString(obj));
	}

	static final class XorShift {
		int x = 123456789;
		int y = 362436069;
		int z = 521288629;
		int w = 88675123;
		static final double TO_DOUBLE = 1.0 / (1L << 31);

		int nextInt(int n) {
			final int t = x ^ (x << 11);
			x = y;
			y = z;
			z = w;
			w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
			final int r = w % n;
			return r < 0 ? r + n : r;
		}

		int nextInt() {
			final int t = x ^ (x << 11);
			x = y;
			y = z;
			z = w;
			w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
			return w;
		}

		boolean nextBoolean() {
			final int t = x ^ (x << 11);
			x = y;
			y = z;
			z = w;
			w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
			return (w & 8) == 0;
		}

		double nextDouble() {
			final int t = x ^ (x << 11);
			x = y;
			y = z;
			z = w;
			w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
			return Math.abs(w * TO_DOUBLE);
		}

		double nextSDouble() {
			final int t = x ^ (x << 11);
			x = y;
			y = z;
			z = w;
			w = (w ^ (w >>> 19)) ^ (t ^ (t >>> 8));
			return w * TO_DOUBLE;
		}
	}

	static final class Timer {
		ArrayList<Long> sum = new ArrayList<Long>();
		ArrayList<Long> start = new ArrayList<Long>();

		void start(int i) {
			if (MEASURE_TIME) {
				while (sum.size() <= i) {
					sum.add(0L);
					start.add(0L);
				}
				start.set(i, System.currentTimeMillis());
			}
		}

		void stop(int i) {
			if (MEASURE_TIME) {
				sum.set(i, sum.get(i) + System.currentTimeMillis() - start.get(i));
			}
		}

		void print() {
			if (MEASURE_TIME && !sum.isEmpty()) {
				System.err.print("[");
				for (int i = 0; i < sum.size(); ++i) {
					System.err.print(sum.get(i) + ", ");
				}
				System.err.println("]");
			}
		}
	}

	static final class Counter {
		ArrayList<Integer> count = new ArrayList<Integer>();

		void add(int i) {
			if (DEBUG) {
				while (count.size() <= i) {
					count.add(0);
				}
				count.set(i, count.get(i) + 1);
			}
		}

		void print() {
			if (DEBUG) {
				System.err.print("[");
				for (int i = 0; i < count.size(); ++i) {
					System.err.print(count.get(i) + ", ");
				}
				System.err.println("]");
			}
		}
	}
}
