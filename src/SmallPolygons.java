import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

public class SmallPolygons {

	private final long startTime = System.currentTimeMillis();
	private static final boolean debug = false;
	private static final int max_tiem = 9000;
	private static final int max_xy = 700;
	private static final double pai2 = Math.atan(1) * 4 * 2;
	private static final double eps = 1e-9;
	private SecureRandom random;
	{
		try {
			random = SecureRandom.getInstance("SHA1PRNG");
			random.setSeed(1);
		} catch (NoSuchAlgorithmException e) {
			e.printStackTrace();
		}
	}
	private int N, NP;
	private Point ps[];
	private Map<Integer, Integer> ids;

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
		Point init = Arrays.stream(t).min((p1, p2) -> p1.y - p2.y).get();
		Point p1 = new Point(init.x, init.y - 1);
		Point p2 = init;
		final List<Point> outside = new ArrayList<>();
		outside.add(init);
		while (true) {
			Point p3 = null;
			double max = -1;
			for (Point p : t) {
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

	// private static long sumt0 = 0;
	// private static long sumt1 = 0;

	Map<Long, Point[]> memo;
	long hashTable[];

	private Point[] polygons(Point[] t) {
		long key = Arrays.stream(t).map(p -> hashTable[ids.get(p.hash())]).reduce(0L, (l1, l2) -> l1 ^ l2);
		Point[] res = memo.get(key);
		if (res != null) {
			return res;
		}

		class Remain {
			final Point p;
			Point t = null, u = null;
			int v = Integer.MAX_VALUE;

			Remain(Point p) {
				this.p = p;
			}
		}

		final List<Edge> checkEdge = new ArrayList<>();
		class Function {

			void setRemain(List<Point> outside, int outsideArea, final Remain r) {
				r.v = Integer.MAX_VALUE;
				r.t = null;
				r.u = null;
				class Pair {
					final int i;
					final Edge e, re1, re2;
					final double d;
					boolean ok = true;

					Pair(int i, Edge e) {
						this.i = i;
						this.e = e;
						this.d = e.dist(r.p);
						re1 = new Edge(r.p, e.p1);
						re2 = new Edge(r.p, e.p2);
					}
				}
				int size = outside.size();
				Pair[] list = new Pair[size];
				for (int i = 0; i < size; i++) {
					list[i] = new Pair(i, new Edge(outside.get(i), outside.get((i + 1) % size)));
				}
				Arrays.sort(list, (o1, o2) -> Double.compare(o1.d, o2.d));

				for (int i = 0; i < size; i++) {
					Pair pair = list[i];
					Edge e = pair.e;
					if (pair.ok) {
						int v = area(outside, outsideArea, pair.i, r.p);
						if (r.v > v && isOK(pair.re1) && isOK(pair.re2)) {
							r.v = v;
							r.t = e.p1;
							r.u = e.p2;
						}
					}
					for (int j = i + 1; j < size; j++) {
						Pair tmpPair = list[j];
						if (tmpPair.ok) {
							tmpPair.ok = !e.intersect(tmpPair.re1) && !e.intersect(tmpPair.re2);
						}
					}
				}
			}

			boolean isOK(Edge e) {
				for (Edge ce : checkEdge)
					if (e.intersect(ce))
						return false;
				return true;
				// return !checkEdge.stream().anyMatch(ce -> e.intersect(ce));
			}
		}
		Function func = new Function();

		List<Point> outside = getOutside(t);
		int outsideArea = area(outside.toArray(new Point[0]));
		List<Remain> remain = new ArrayList<>();
		Set<Point> outsideSet = new HashSet<>(outside);
		for (Point p : t) {
			if (outsideSet.contains(p))
				continue;
			Remain r = new Remain(p);
			remain.add(r);
			func.setRemain(outside, outsideArea, r);
		}
		while (!remain.isEmpty()) {
			Collections.sort(remain, (o1, o2) -> o1.v - o2.v);
			Remain r = remain.get(0);
			remain.remove(r);
			if (r.t == null || r.u == null) {
				// うまく全ての頂点が使えなかったケース
				// 0.01%くらいしかなさそう
				return null;
			}
			for (int i = 0, size = outside.size(); i < size; i++) {
				if (outside.get(i) == r.t) {
					outsideArea = area(outside, outsideArea, i, r.p);
					outside.add(i + 1, r.p);
					for (Edge e : checkEdge) {
						if (e.p1 == r.t && e.p2 == r.u) {
							checkEdge.remove(e);
							break;
						}
					}
					Edge e0 = new Edge(r.t, r.p);
					Edge e1 = new Edge(r.p, r.u);
					checkEdge.add(e0);
					checkEdge.add(e1);
					for (Remain x : remain) {
						// 線分上の点はそのまま使うしか無い
						if (e0.intersect(x.p)) {
							x.v = 0;
							x.t = r.t;
							x.u = r.p;
						} else if (e1.intersect(x.p)) {
							x.v = 0;
							x.t = r.p;
							x.u = r.u;
						} else {
							Edge te0 = x.t == null ? null : new Edge(x.t, x.p);
							Edge te1 = x.u == null ? null : new Edge(x.p, x.u);
							if (te0 == null || te1 == null || (r.t == x.t && r.u == x.u) || e0.intersect(te0)
									|| e0.intersect(te1) || e1.intersect(te0) || e1.intersect(te1)
									|| func.isOK(new Edge(r.p, x.p))) {
								func.setRemain(outside, outsideArea, x);
							}
						}
					}
					break;
				}
			}
		}
		res = outside.toArray(new Point[0]);
		memo.put(key, res);
		return res;
	}

	private static final int areaFunc(Point p0, Point p1) {
		return (p1.y + p0.y) * (p1.x - p0.x);
	}

	private int area(List<Point> poly, int polyArea, int index, Point p) {
		int size = poly.size();
		Point p0 = poly.get(index);
		Point p1 = poly.get((index + 1) % size);
		polyArea += -areaFunc(p0, p1) + areaFunc(p0, p) + areaFunc(p, p1);
		return Math.abs(polyArea);
	}

	private int area(Point[] poly) {
		int s = 0;
		for (int i = 0, n = poly.length; i < n; i++) {
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
		for (int i = 0; i < NP; i++) {
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
				if (badCount > 50) {
					badCount = 0;
					--N;
				}
			}
			{
				long tmp = System.currentTimeMillis() - startTime;
				maxOneTime = Math.max(maxOneTime, tmp - time);
				time = tmp;
				if (time + maxOneTime * 2 >= max_tiem) {
					break;
				}
			}

			Point[] x = new Point[N];
			List<Point> tmp[] = new List[N];
			for (int i = 0; i < N; i++) {
				tmp[i] = new ArrayList<>();
				x[i] = Point.random(random);
			}
			for (int i = 0; i < NP; i++) {
				int t = -1;
				double dist = Double.MAX_VALUE / 2;
				for (int j = 0; j < N; j++) {
					double tmpd = G2D.dist(x[j], ps[i]);
					if (dist > tmpd) {
						dist = tmpd;
						t = j;
					}
				}
				tmp[t].add(ps[i]);
			}
			if (Arrays.stream(tmp).anyMatch(list -> list.size() < 3))
				continue NG;

			Point restmp[][] = new Point[N][];
			int value = 0;
			valueCount++;
			for (int i = 0; i < N; i++) {
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
		if (debug) {
			// System.out.println(sumt0 + "\n" + sumt1);
			System.out.println("values = " + valueCount);
		}
		return result(res);
	}

	private String[] result(Point polys[][]) {
		String res[] = new String[polys.length];
		for (int i = 0; i < polys.length; i++) {
			res[i] = Arrays
					.stream(polys[i])
					.map(point -> ids.get(point.hash()))
					.collect(() -> new StringJoiner(" "), (joiner, id) -> joiner.add(Integer.toString(id)),
							(j1, j2) -> j1.merge(j2)).toString();
		}
		return res;
	}

	private static class Point {
		public final int x, y;

		public Point(int x, int y) {
			this.x = x;
			this.y = y;
		}

		static Point random(SecureRandom random) {
			return new Point(random.nextInt(max_xy), random.nextInt(max_xy));
		}

		public int hash() {
			return (x << 16) | y;
		}

		public String toString() {
			return "[ " + x + ", " + y + " ]";
		}
	}

	private static class G2D {
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

	private static class Edge {
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
	}
}
