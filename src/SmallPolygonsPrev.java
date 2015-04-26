import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

public class SmallPolygonsPrev {

	private final long startTime = System.currentTimeMillis();
	private static final boolean DEBUG = false;
	private static final boolean MEASURE_TIME = true;
	private static final int MAX_TIME = 9500;
	private static final int MAX_XY = 700;
	private static final int BEAM_WIDTH = 2;
	private static final double pai2 = Math.atan(1) * 4 * 2;
	private static final double eps = 1e-9;
	private final XorShift random = new XorShift();
	private final XorShift random2 = new XorShift();
	private final Timer timer = new Timer();
	private int N, NP;
	private Point ps[];
	private Map<Integer, Integer> ids;

	Map<Long, Point[]> memo;
	long hashTable[];

	private abstract class IntComparable implements Comparable<IntComparable> {
		int value = Integer.MAX_VALUE / 2;

		@Override
		public int compareTo(IntComparable o) {
			return value - o.value;
		}
	}

	private Point[] polygons(Point[] t) {
		long key = 0;
		for (int i = 0, size = t.length; i < size; ++i)
			key ^= hashTable[ids.get(t[i].hash())];
		Point[] res = memo.get(key);
		if (res != null) {
			return res;
		}

		class Remain extends IntComparable {
			final Point p;
			Point t = null, u = null;

			Remain(Point p) {
				this.p = p;
			}

			Remain(Remain r) {
				p = r.p;
				t = r.t;
				u = r.u;
				value = r.value;
			}
		}

		class Function {
			void setRemain(List<Point> outside, List<Edge> checkEdge, final Remain r) {
				for (int i = 0, size = outside.size(); i < size; ++i) {
					Point a = outside.get(i);
					Point b = outside.get((i + 1) % size);
					int v = areaDiff(a, b, r.p);
					if (r.value > v && isOK(checkEdge, new Edge(r.p, a)) && isOK(checkEdge, new Edge(r.p, b))) {
						r.value = v;
						r.t = a;
						r.u = b;
					}
				}
			}

			boolean isOK(List<Edge> checkEdge, Edge e) {
				for (int i = 0, size = checkEdge.size(); i < size; ++i)
					if (e.intersect(checkEdge.get(i)))
						return false;
				return true;
			}

			<T extends IntComparable> void partition(List<T> list, int lim) {
				int r = list.size();
				int l = 0;
				if (lim >= r)
					return;
				while (true) {
					if (lim == 0 || lim == r - l)
						break;
					int pp = random2.nextInt(r - l) + l;
					T pivot = list.get(pp);
					list.set(pp, list.get(l));
					list.set(l, pivot);
					int right = r;
					int left = l + 1;
					while (left < right) {
						boolean move = pivot.compareTo(list.get(left)) <= 0;
						if (move) {
							--right;
							T tmp = list.get(right);
							list.set(right, list.get(left));
							list.set(left, tmp);
						} else {
							++left;
						}
					}
					int large = right - l;
					if (large == lim)
						break;
					if (large > lim) {
						r = right;
					} else {
						l = right;
						lim -= large;
					}
				}
			}
		}
		Function func = new Function();

		class Polygon extends IntComparable {
			final List<Point> outside;
			final List<Remain> remain;
			final List<Edge> checkEdge;
			int outsideArea;

			Polygon(List<Point> outside, List<Remain> remain, List<Edge> checkEdge, int outsideArea) {
				this.outside = outside;
				this.remain = remain;
				this.checkEdge = checkEdge;
				this.outsideArea = outsideArea;
			}

			Polygon(Polygon p) {
				outside = new ArrayList<>(p.outside);
				remain = new ArrayList<>(p.remain.size());
				for (int i = 0, size = p.remain.size(); i < size; ++i)
					remain.add(new Remain(p.remain.get(i)));
				checkEdge = new ArrayList<>(p.checkEdge);
				outsideArea = p.outsideArea;
				value = p.value;
			}

			void next(int index) {
				Remain r = remain.remove(index);
				int minReaminValue = Integer.MAX_VALUE / 2;
				for (int i = 0, size = outside.size(); i < size; ++i) {
					if (outside.get(i) == r.t) {
						outsideArea += areaDiff(outside.get(i), outside.get((i + 1) % size), r.p);
						outside.add(i + 1, r.p);
						for (int j = 0, j_size = checkEdge.size(); j < j_size; ++j) {
							Edge e = checkEdge.get(j);
							if (e.p1 == r.t && e.p2 == r.u) {
								checkEdge.remove(e);
								break;
							}
						}
						Edge e0 = new Edge(r.t, r.p);
						Edge e1 = new Edge(r.p, r.u);
						checkEdge.add(e0);
						checkEdge.add(e1);
						Collections.sort(checkEdge);
						for (int j = 0, j_size = remain.size(); j < j_size; ++j) {
							Remain x = remain.get(j);
							// ÃÂ§ÃÂ·ÃÂÃÂ¥ÃÂÃÂÃÂ¤ÃÂ¸ÃÂÃÂ£ÃÂÃÂ®ÃÂ§ÃÂÃÂ¹ÃÂ£ÃÂÃÂ¯ÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂ®ÃÂ£ÃÂÃÂ¾ÃÂ£ÃÂÃÂ¾ÃÂ¤ÃÂ½ÃÂ¿ÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂÃÂ§ÃÂÃÂ¡ÃÂ£ÃÂÃÂ
							if (e0.intersect(x.p)) {
								x.value = 0;
								x.t = r.t;
								x.u = r.p;
							} else if (e1.intersect(x.p)) {
								x.value = 0;
								x.t = r.p;
								x.u = r.u;
							} else {
								Edge te0 = x.t == null ? null : new Edge(x.t, x.p);
								Edge te1 = x.u == null ? null : new Edge(x.p, x.u);
								if (te0 == null || te1 == null || (r.t == x.t && r.u == x.u) || e0.intersect(te0)
										|| e0.intersect(te1) || e1.intersect(te0) || e1.intersect(te1)) {
									x.value = Integer.MAX_VALUE / 2;
									x.t = null;
									x.u = null;
									func.setRemain(outside, checkEdge, x);
								} else if (func.isOK(checkEdge, new Edge(r.p, x.p))) {
									for (int q = i; q < i + 2; ++q) {
										int w = q % outside.size();
										Point a = outside.get(w);
										Point b = outside.get((w + 1) % outside.size());
										int v = areaDiff(a, b, x.p);
										if (x.value > v && func.isOK(checkEdge, new Edge(x.p, a))
												&& func.isOK(checkEdge, new Edge(x.p, b))) {
											x.value = v;
											x.t = a;
											x.u = b;
										}
									}
								}
							}
							minReaminValue = Math.min(minReaminValue, x.value);
						}
						break;
					}
				}
				value = outsideArea + minReaminValue;
			}
		}

		List<Point> outside = getOutside(t);
		List<Edge> checkEdge = new ArrayList<>();
		int outsideArea = area(outside.toArray(new Point[0]));
		List<Remain> remain = new ArrayList<>();
		Set<Point> outsideSet = new HashSet<>(outside);
		for (int i = 0, size = t.length; i < size; ++i) {
			Point p = t[i];
			if (outsideSet.contains(p))
				continue;
			Remain r = new Remain(p);
			remain.add(r);
			func.setRemain(outside, checkEdge, r);
		}
		List<Polygon> polys = new ArrayList<>();
		polys.add(new Polygon(outside, remain, checkEdge, outsideArea));
		for (int i = 0, size = remain.size(); i < size; ++i) {
			List<Polygon> next = new ArrayList<>();
			for (int j = 0, j_size = Math.min(BEAM_WIDTH, polys.size()); j < j_size; ++j) {
				Polygon now_p = polys.get(j);
				Collections.sort(now_p.remain);
				// partition(now_p.remain, 10);
				for (int k = 0, k_size = Math.min(5, now_p.remain.size()); k < k_size; ++k) {
					Remain check = now_p.remain.get(k);
					if (check.t == null || check.u == null) {
						// ÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂ¾ÃÂ£ÃÂÃÂÃÂ¥ÃÂÃÂ¨ÃÂ£ÃÂÃÂ¦ÃÂ£ÃÂÃÂ®ÃÂ©ÃÂ ÃÂÃÂ§ÃÂÃÂ¹ÃÂ£ÃÂÃÂÃÂ¤ÃÂ½ÃÂ¿ÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂªÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂ£ÃÂ£ÃÂÃÂÃÂ£ÃÂÃÂ±ÃÂ£ÃÂÃÂ¼ÃÂ£ÃÂÃÂ¹
						continue;
					}
					Polygon p = new Polygon(now_p);
					p.next(k);
					next.add(p);
				}
			}
			polys = next;
			if (polys.isEmpty()) {
				return null;
			}
			Collections.sort(polys);
			// partition(polys, BEAM_WIDTH);
		}
		res = polys.get(0).outside.toArray(new Point[0]);
		memo.put(key, res);
		return res;
	}

	private static final int areaFunc(Point p0, Point p1) {
		return (p1.y + p0.y) * (p1.x - p0.x);
	}

	private int areaDiff(Point p0, Point p1, Point p) {
		return -areaFunc(p0, p1) + areaFunc(p0, p) + areaFunc(p, p1);
	}

	private int area(Point[] poly) {
		int s = 0;
		for (int i = 0, n = poly.length; i < n; ++i) {
			s += areaFunc(poly[i], poly[(i + 1) % n]);
		}
		return Math.abs(s);
	}

	String[] choosePolygons(int[] points, int N_) {
		this.N = N_;
		NP = points.length / 2;
		N = Math.min(N, NP / 3);
		ps = new Point[NP];
		ids = new HashMap<>();
		memo = new HashMap<>();
		hashTable = new long[NP];
		for (int i = 0; i < NP; ++i) {
			ps[i] = new Point(points[i * 2], points[i * 2 + 1]);
			ids.put(ps[i].hash(), i);
			hashTable[i] = random.nextLong();
		}

		int min = Integer.MAX_VALUE;
		Point res[][] = null;
		long time = System.currentTimeMillis() - startTime;
		int badCount = 0, valueCount = 0;
		long maxOneTime = 0;
		NG: while (true) {
			if (res == null) {
				++badCount;
				if (badCount > 40) {
					badCount = 0;
					--N;
				}
			}
			{
				long tmp = System.currentTimeMillis() - startTime;
				maxOneTime = Math.max(maxOneTime, tmp - time);
				time = tmp;
				if (time + maxOneTime >= MAX_TIME) {
					break;
				}
			}

			Point[] x = new Point[N];
			List<Point> tmp[] = new List[N];
			for (int i = 0; i < N; ++i) {
				tmp[i] = new ArrayList<>();
				x[i] = Point.random(random);
			}
			for (int i = 0; i < NP; ++i) {
				int t = -1;
				double dist = Double.MAX_VALUE / 2;
				for (int j = 0; j < N; ++j) {
					double tmpd = G2D.dist(x[j], ps[i]);
					if (dist > tmpd) {
						dist = tmpd;
						t = j;
					}
				}
				tmp[t].add(ps[i]);
			}
			for (int i = 0, size = tmp.length; i < size; ++i)
				if (tmp[i].size() < 3)
					continue NG;

			Point restmp[][] = new Point[N][];
			int value = 0;
			valueCount++;
			for (int i = 0; i < N; ++i) {
				Point polys[] = polygons(tmp[i].toArray(new Point[0]));
				if (polys == null)
					continue NG;
				double a = area(polys);
				if (a < eps)
					continue NG;
				restmp[i] = polys;
				value += a;
				if (min <= value)
					continue NG;
			}
			min = value;
			res = restmp;
		}
		if (DEBUG) {
			System.out.println("values = " + valueCount);
			timer.print();
		}
		return result(res);
	}

	private String[] result(Point polys[][]) {
		String res[] = new String[polys.length];
		for (int i = 0; i < polys.length; ++i) {
			StringJoiner joiner = new StringJoiner(" ");
			for (int j = 0, j_size = polys[i].length; j < j_size; ++j)
				joiner.add(Integer.toString(ids.get(polys[i][j].hash())));
			res[i] = joiner.toString();
		}
		return res;
	}

	private static final class Point {
		public final int x, y;

		public Point(int x, int y) {
			this.x = x;
			this.y = y;
		}

		static Point random(XorShift random) {
			return new Point(random.nextInt(MAX_XY), random.nextInt(MAX_XY));
		}

		public int hash() {
			return (x << 16) | y;
		}

		public String toString() {
			return "[ " + x + ", " + y + " ]";
		}
	}

	private static final class G2D {
		public static Point sub(Point p1, Point p2) {
			return new Point(p1.x - p2.x, p1.y - p2.y);
		}

		public static double norm(int x, int y) {
			return Math.sqrt(x * x + y * y);
		}

		public static int dot(Point p1, Point p2) {
			return p1.x * p2.x + p1.y * p2.y;
		}

		public static int cross(Point p1, Point p2) {
			return p1.x * p2.y - p1.y * p2.x;
		}

		public static double dist(Point p1, Point p2) {
			return norm(p1.x - p2.x, p1.y - p2.y);
		}
	}

	private static final class Edge implements Comparable<Edge> {
		public Point p1, p2, vect; //vector p1 -> p2
		public double norm;

		public Edge(Point p1n, Point p2n) {
			p1 = p1n;
			p2 = p2n;
			vect = G2D.sub(p2, p1);
			norm = G2D.norm(vect.x, vect.y);
		}

		public String toString() {
			return p1 + " " + p2;
		}

		boolean eq(double a, double b) {
			return Math.abs(a - b) < eps;
		}

		public boolean intersect(Edge other) {
			//do edges "this" and "other" intersect?
			if (Math.min(p1.x, p2.x) > Math.max(other.p1.x, other.p2.x)
					|| Math.max(p1.x, p2.x) < Math.min(other.p1.x, other.p2.x)
					|| Math.min(p1.y, p2.y) > Math.max(other.p1.y, other.p2.y)
					|| Math.max(p1.y, p2.y) < Math.min(other.p1.y, other.p2.y)) {
				return false;
			}

			int den = other.vect.y * vect.x - other.vect.x * vect.y;
			// parallel edges
			if (den == 0) {
				if (Math.min(other.dist2(this), dist2(other)) > 0) {
					return false;
				}
				//on the same line - "not intersect" only if one of the vertices is common,
				//and the other doesn't belong to the line
				if ((p1 == other.p1 && eq(G2D.dist(p2, other.p2), norm + other.norm))
						|| (p1 == other.p2 && eq(G2D.dist(p2, other.p1), norm + other.norm))
						|| (p2 == other.p1 && eq(G2D.dist(p1, other.p2), norm + other.norm))
						|| (p2 == other.p2 && eq(G2D.dist(p1, other.p1), norm + other.norm))) {
					return false;
				}
				return true;
			}
			//common vertices
			if (p1 == other.p1 || p1 == other.p2 || p2 == other.p1 || p2 == other.p2) {
				return false;
			}

			int u1 = other.vect.x * (p1.y - other.p1.y) - other.vect.y * (p1.x - other.p1.x);
			int u2 = vect.x * (p1.y - other.p1.y) - vect.y * (p1.x - other.p1.x);
			if ((den < 0 && (u1 > 0 || u1 < den || u2 > 0 || u2 < den) || (den > 0 && (u1 < 0 || u1 > den || u2 < 0 || u2 > den)))) {
				return false;
			}
			return true;
		}

		public boolean intersect(Point p) {
			return !(p1 == p || p2 == p || Math.min(p1.x, p2.x) > p.x || Math.max(p1.x, p2.x) < p.x
					|| Math.min(p1.y, p2.y) > p.y || Math.max(p1.y, p2.y) < p.y || dist(p) > 0);
		}

		// ---------------------------------------------------
		public double dist(Point p) {
			//distance from p to the edge
			if (G2D.dot(vect, G2D.sub(p, p1)) <= 0)
				return G2D.dist(p, p1); //from p to p1
			if (G2D.dot(vect, G2D.sub(p, p2)) >= 0)
				return G2D.dist(p, p2); //from p to p2
			//distance to the line itself
			return Math.abs(-vect.y * p.x + vect.x * p.y + p1.x * p2.y - p1.y * p2.x) / norm;
		}

		// ---------------------------------------------------
		public double dist2(Edge other) {
			//distance from the closest of the endpoints of "other" to "this"
			return Math.min(dist(other.p1), dist(other.p2));
		}

		@Override
		public int compareTo(Edge o) {
			return Double.compare(o.norm, norm);
		}
	}

	private static double angle(Point a, Point b, Point c) {
		Point v1 = G2D.sub(b, a);
		Point v2 = G2D.sub(b, c);
		return Math.atan2(G2D.cross(v1, v2), G2D.dot(v1, v2));
	}

	private static double angle2(Point a, Point b, Point c) {
		double x = angle(a, b, c);
		if (x < 0) {
			x = pai2 + x;
		}
		return x;
	}

	private List<Point> getOutside(Point[] t) {
		Point init = t[0];
		for (int i = 1, size = t.length; i < size; ++i)
			if (init.y > t[i].y)
				init = t[i];
		Point p1 = new Point(init.x, init.y - 1);
		Point p2 = init;
		final List<Point> outside = new ArrayList<>();
		outside.add(init);
		while (true) {
			Point p3 = null;
			double max = -1;
			for (int i = 0, size = t.length; i < size; ++i) {
				Point p = t[i];
				if (p1 == p || p2 == p)
					continue;
				double a = angle2(p1, p2, p);
				if (max < a || (p3 != null && max - a < eps && G2D.dist(p2, p) < G2D.dist(p2, p3))) {
					max = a;
					p3 = p;
				}
			}
			if (init == p3)
				break;
			else {
				outside.add(p3);
				p1 = p2;
				p2 = p3;
			}
		}
		return outside;
	}

	private static final class XorShift {
		int x = 123456789;
		int y = 362436069;
		int z = 521288629;
		int w = 88675123;

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

		long nextLong() {
			return ((long) nextInt() << 32) | nextInt();
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
}
