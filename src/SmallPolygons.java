import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;

public class SmallPolygons {

	private final long startTime = System.currentTimeMillis();
	private static final int max_tiem = 9000;
	private static final int max_xy = 700;
	private static final double pai = Math.atan(1) * 4;
	private static final double eps = 1e-9;
	private static final Random random = new ContestXorShift(0);
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
			x = pai * 2 + x;
		}
		return x;
	}

	private List<Point> getOutside(Point[] t) {
		Point init = null;
		int min = Integer.MAX_VALUE;
		for (Point p : t) {
			if (min > p.y) {
				min = p.y;
				init = p;
			}
		}
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

	//	private static long sumt0 = 0;
	//	private static long sumt1 = 0;

	private Point[] polygons(Point[] t) {
		class Remain implements Comparable<Remain> {
			final Point p;
			Point t = null, u = null;
			int v = Integer.MAX_VALUE;

			Remain(Point p) {
				this.p = p;
			}

			@Override
			public int compareTo(Remain o) {
				return v - o.v;
			}
		}

		final List<Point> outside = getOutside(t);
		final List<Edge> checkEdge = new ArrayList<>();
		class Function {

			void setRemain(final Remain r) {
				r.v = Integer.MAX_VALUE;
				r.t = null;
				r.u = null;
				class Pair implements Comparable<Pair> {
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

					@Override
					public int compareTo(Pair o) {
						return Double.compare(d, o.d);
					}
				}
				int size = outside.size();
				List<Pair> list = new ArrayList<>();
				for (int i = 0; i < size; i++) {
					list.add(new Pair(i, new Edge(outside.get(i), outside.get((i + 1) % size))));
				}
				Collections.sort(list);

				for (int i = 0; i < size; i++) {
					Pair pair = list.get(i);
					Edge e = pair.e;
					if (pair.ok) {
						int v = area(outside, pair.i, r.p);
						if (r.v > v && isOK(pair.re1) && isOK(pair.re2)) {
							r.v = v;
							r.t = e.p1;
							r.u = e.p2;
						}
					}
					for (int j = i + 1; j < size; j++) {
						Pair tmpPair = list.get(j);
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
			}
		}
		Function func = new Function();

		List<Remain> remain = new ArrayList<>();
		Set<Point> outsideSet = new HashSet<>(outside);
		for (Point p : t) {
			if (outsideSet.contains(p))
				continue;
			Remain r = new Remain(p);
			remain.add(r);
			func.setRemain(r);
		}
		while (!remain.isEmpty()) {
			Collections.sort(remain);
			Remain r = remain.get(0);
			remain.remove(r);
			if (r.t == null || r.u == null) {
				return null;
				// throw new RuntimeException();
			}
			for (int i = 0, size = outside.size(); i < size; i++) {
				if (outside.get(i) == r.t) {
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
								func.setRemain(x);
							}
						}
					}
					break;
				}
			}
		}
		return outside.toArray(new Point[0]);
	}

	private int area(List<Point> poly, int index, Point p) {
		int s = 0;
		for (int i = 0, n = poly.size(); i < n; i++) {
			Point p0 = poly.get(i);
			Point p1 = poly.get((i + 1) % n);
			if (index != i) {
				s += (p1.y + p0.y) * (p1.x - p0.x);
			} else {
				s += (p.y + p0.y) * (p.x - p0.x) + (p1.y + p.y) * (p1.x - p.x);
			}
		}
		return Math.abs(s);
	}

	private int area(Point[] poly) {
		int s = 0;
		for (int i = 0, n = poly.length; i < n; i++) {
			Point p0 = poly[i];
			Point p1 = poly[(i + 1) % n];
			s += (p1.y + p0.y) * (p1.x - p0.x);
		}
		return Math.abs(s);
	}

	String[] choosePolygons(int[] points, int N_) {
		this.N = N_;
		NP = points.length / 2;
		N = Math.min(N, NP / 3);
		ps = new Point[NP];
		ids = new HashMap<>();
		for (int i = 0; i < NP; i++) {
			ps[i] = new Point(points[i * 2], points[i * 2 + 1]);
			ids.put(ps[i].hash(), i);
		}

		int min = Integer.MAX_VALUE;
		Point res[][] = null;
		long time = System.currentTimeMillis() - startTime;
		int count = 0;
		long maxOneTime = 0;
		NG: while (true) {
			++count;
			if (res == null && count > 50) {
				count = 0;
				--N;
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
				x[i] = Point.random();
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
			for (int i = 0; i < N; i++)
				if (tmp[i].size() < 3)
					continue NG;

			Point restmp[][] = new Point[N][];
			int value = 0;
			for (int i = 0; i < N; i++) {
				Point polys[] = polygons(tmp[i].toArray(new Point[0]));
				if (polys == null)
					continue NG;
				restmp[i] = polys;
				double a = area(polys);
				if (a < eps) {
					continue NG;
				}
				value += a;
			}
			if (min > value) {
				min = value;
				res = restmp;
			}
		}
		// System.out.println(sumt0 + "\n" + sumt1);
		return result(res);
	}

	private String[] result(Point polys[][]) {
		String res[] = new String[polys.length];
		for (int i = 0; i < polys.length; i++) {
			int n = polys[i].length;
			int list[] = new int[n];
			for (int j = 0; j < n; j++) {
				list[j] = ids.get(polys[i][j].hash());
			}
			res[i] = toString(list);
		}
		return res;
	}

	private String toString(int list[]) {
		StringJoiner sj = new StringJoiner(" ");
		for (int i : list) {
			sj.add(Integer.toString(i));
		}
		return sj.toString();
	}

	private static class ContestXorShift extends Random {
		private static final long serialVersionUID = -8807494513400211599L;
		private long x, y, z, w;

		private void init() {
			x = 123456789;
			y = 362436069;
			z = 521288629;
			w = 88675123;
		}

		public ContestXorShift(long seed) {
			super(seed);
			init();
			x = seed;
		}

		public synchronized void setSeed(long seed) {
			super.setSeed(seed);
			init();
			x = seed;
		}

		protected int next(int bits) {
			long t = (x ^ x << 11) & (1L << 32) - 1;
			x = y;
			y = z;
			z = w;
			w = (w ^ w >>> 19 ^ t ^ t >>> 8) & (1L << 32) - 1;
			return (int) w >>> 32 - bits;
		}
	}

	private static class Point {
		public final int x, y;

		public Point(int x, int y) {
			this.x = x;
			this.y = y;
		}

		static Point random() {
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

		public static double norm(Point p) {
			return Math.sqrt(p.x * p.x + p.y * p.y);
		}

		public static int dot(Point p1, Point p2) {
			return p1.x * p2.x + p1.y * p2.y;
		}

		public static int cross(Point p1, Point p2) {
			return p1.x * p2.y - p1.y * p2.x;
		}

		public static double dist(Point p1, Point p2) {
			return norm(sub(p1, p2));
		}
	}

	private static class Edge {
		public Point p1, p2, vect; //vector p1 -> p2
		public double norm;

		public Edge(Point p1n, Point p2n) {
			p1 = p1n;
			p2 = p2n;
			vect = G2D.sub(p2, p1);
			norm = G2D.norm(vect);
		}

		public String toString() {
			return p1 + " " + p2;
		}

		boolean eq(double a, double b) {
			return Math.abs(a - b) < eps;
		}

		// ---------------------------------------------------
		//		public boolean intersect(Edge other) {
		//			long start = System.nanoTime();
		//			boolean res1 = intersect_(other);
		//			long t1 = System.nanoTime();
		//			boolean res2 = intersectOrigin(other);
		//			long t2 = System.nanoTime();
		//			if (res1 != res2) {
		//				System.err.println("wrong " + res1 + " " + res2);
		//			}
		//			sumt0 += (t1 - start);
		//			sumt1 += (t2 - t1);
		//			return res1;
		//		}

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

		//		public boolean intersectOrigin(Edge other) {
		//			//do edges "this" and "other" intersect?
		//			if (Math.min(p1.x, p2.x) > Math.max(other.p1.x, other.p2.x)) {
		//				return false;
		//			}
		//			if (Math.max(p1.x, p2.x) < Math.min(other.p1.x, other.p2.x)) {
		//				return false;
		//			}
		//			if (Math.min(p1.y, p2.y) > Math.max(other.p1.y, other.p2.y)) {
		//				return false;
		//			}
		//			if (Math.max(p1.y, p2.y) < Math.min(other.p1.y, other.p2.y)) {
		//				return false;
		//			}
		//
		//			int den = other.vect.y * vect.x - other.vect.x * vect.y;
		//			int num1 = other.vect.x * (p1.y - other.p1.y) - other.vect.y * (p1.x - other.p1.x);
		//			int num2 = vect.x * (p1.y - other.p1.y) - vect.y * (p1.x - other.p1.x);
		//
		//			//parallel edges
		//			if (den == 0) {
		//				if (Math.min(other.dist2(this), dist2(other)) > 0) {
		//					return false;
		//				}
		//				//on the same line - "not intersect" only if one of the vertices is common,
		//				//and the other doesn't belong to the line
		//				if ((this.p1 == other.p1 && eq(G2D.dist(this.p2, other.p2), this.norm + other.norm))
		//						|| (this.p1 == other.p2 && eq(G2D.dist(this.p2, other.p1), this.norm + other.norm))
		//						|| (this.p2 == other.p1 && eq(G2D.dist(this.p1, other.p2), this.norm + other.norm))
		//						|| (this.p2 == other.p2 && eq(G2D.dist(this.p1, other.p1), this.norm + other.norm))) {
		//					return false;
		//				}
		//				return true;
		//			}
		//
		//			//common vertices
		//			if (this.p1 == other.p1 || this.p1 == other.p2 || this.p2 == other.p1 || this.p2 == other.p2) {
		//				return false;
		//			}
		//
		//			double u1 = (double) num1 / den;
		//			double u2 = (double) num2 / den;
		//			if (u1 < 0 || u1 > 1 || u2 < 0 || u2 > 1) {
		//				return false;
		//			}
		//			return true;
		//		}

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
