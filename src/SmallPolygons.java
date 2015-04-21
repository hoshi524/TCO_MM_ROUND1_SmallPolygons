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

	static final double pai = Math.atan(1) * 4;
	static final double eps = 1e-10;
	Random random = new ContestXorShift(0);
	int N, NP, points[];
	Point ps[];
	Map<Integer, Integer> ids;

	//	public static final void main(String args[]) {
	//		new SmallPolygonsVis().run(new int[] { 646, 554, 642, 594, 631, 601, 634, 633, 660, 624, 660, 628, 644, 659, 648, 672, 635, 662,
	//				610, 650, 610, 699, 697, 694, 692, 577, 696, 558, 669, 561, 610, 653 }, 1);
	//	}

	static double angle(Point a, Point b, Point c) {
		Point v1 = G2D.sub(b, a);
		Point v2 = G2D.sub(b, c);
		return Math.atan2(G2D.cross(v1, v2), G2D.dot(v1, v2));
	}

	static double angle2(Point a, Point b, Point c) {
		double x = angle(a, b, c);
		if (x < 0) {
			x = pai * 2 + x;
		}
		return x;
	}

	Point[] polygons(Point[] t) {
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
				if (max < a || (p3 != null && Math.abs(max - a) < eps && G2D.dist(p2, p) < G2D.dist(p2, p3))) {
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
		class Remain implements Comparable<Remain> {
			final Point p;
			Point t = null, u = null;
			double d = Double.MAX_VALUE / 2;

			Remain(Point p) {
				this.p = p;
			}

			@Override
			public int compareTo(Remain o) {
				return Double.compare(d, o.d);
			}
		}
		List<Remain> remain = new ArrayList<>();
		Set<Point> outsideSet = new HashSet<>(outside);

		class Function {
			/*
			 * 重い
			 */
			void setRemain(Remain r) {
				r.d = Double.MAX_VALUE / 2;
				r.t = null;
				r.u = null;
				for (int i = 0, size = outside.size(); i < size; i++) {
					Point a = outside.get(i);
					Point b = outside.get((i + 1) % size);
					double d = G2D.dist(a, b, r.p);
					if (r.d > d && isOK(a, r.p, b)) {
						r.d = d;
						r.t = a;
						r.u = b;
					}
				}
			}

			boolean isOK(Point a, Point b, Point c) {
				Edge e1 = new Edge(b, a);
				Edge e2 = new Edge(b, c);
				for (int i = 0, size = outside.size(); i < size; i++) {
					Edge e = new Edge(outside.get(i), outside.get((i + 1) % size));
					if (e.intersect(e1) || e.intersect(e2)) {
						return false;
					}
				}
				return true;
			}
		}

		Function func = new Function();
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
				throw new RuntimeException();
			}
			for (int i = 0, size = outside.size(); i < size; i++) {
				if (outside.get(i) == r.t) {
					Point a = r.t;
					Point b = r.p;
					Point c = r.u;
					outside.add(i + 1, r.p);
					Edge newE0 = new Edge(r.p, r.t);
					Edge newE1 = new Edge(r.p, r.u);
					for (Remain x : remain) {
						Edge xe0 = new Edge(x.p, x.t);
						Edge xe1 = new Edge(x.p, x.u);
						if (xe0.intersect(newE0) || xe0.intersect(newE1) || xe1.intersect(newE0) || xe1.intersect(newE1)) {
							x.d = Double.MAX_VALUE / 2;
						}
						double d;
						d = G2D.dist(a, b, x.p);
						if (x.d > d && func.isOK(a, x.p, b)) {
							x.d = d;
							x.t = a;
							x.u = b;
						}
						d = G2D.dist(b, c, x.p);
						if (x.d > d && func.isOK(b, x.p, c)) {
							x.d = d;
							x.t = b;
							x.u = c;
						}
					}
					break;
				}
			}
		}
		return outside.toArray(new Point[0]);
	}

	String[] choosePolygons(int[] points, int N) {
		NP = points.length / 2;
		N = Math.min(N, NP / 3);
		this.N = N;
		this.points = points;
		ps = new Point[NP];
		ids = new HashMap<>();
		for (int i = 0; i < NP; i++) {
			ps[i] = new Point(points[i * 2], points[i * 2 + 1]);
			ids.put(ps[i].hash(), i);
		}
		Point best[] = new Point[N];
		double value = 0;
		for (int i = 0; i < 0xffff; i++) {
			Point p[] = new Point[N];
			Set<Integer> used = new HashSet<>();
			for (int j = 0; j < N; j++) {
				while (true) {
					int id = random.nextInt(NP);
					if (!used.contains(id)) {
						used.add(id);
						p[j] = ps[id];
						break;
					}
				}
			}
			double tmp = dist(p);
			if (value < tmp) {
				value = tmp;
				best = p;
			}
		}
		@SuppressWarnings("unchecked")
		List<Point> split[] = new List[N];
		Set<Point> used = new HashSet<>();
		for (int i = 0; i < N; i++) {
			split[i] = new ArrayList<>();
			split[i].add(best[i]);
			used.add(best[i]);
		}
		for (int i = 0; i < N; i++) {
			while (true) {
				double dist = Double.MAX_VALUE / 2;
				Point t = null;
				for (Point p : ps) {
					if (!used.contains(p)) {
						double tmp = G2D.dist(best[i], p);
						if (dist > tmp) {
							dist = tmp;
							t = p;
						}
					}
				}
				if (t == null) {
					throw new RuntimeException();
				}
				used.add(t);
				split[i].add(t);

				if (split[i].size() >= 3) {
					Point min = new Point(0, Integer.MAX_VALUE / 2), max = new Point(0, Integer.MIN_VALUE / 2);
					for (Point p : split[i]) {
						if (min.y > p.y)
							min = p;
						if (max.y < p.y)
							max = p;
					}
					double base = G2D.dist(min, max) + eps;
					boolean ok = false;
					for (Point p : split[i]) {
						ok |= G2D.dist(min, p) + G2D.dist(p, max) > base;
					}
					if (ok)
						break;
				}
			}
		}
		for (Point p : ps) {
			if (!used.contains(p)) {
				List<Point> t = null;
				double dist = Double.MAX_VALUE / 2;
				for (int i = 0; i < N; i++) {
					double tmp = G2D.dist(split[i].get(0), p);
					if (dist > tmp) {
						dist = tmp;
						t = split[i];
					}
				}
				t.add(p);
				used.add(p);
			}
		}
		Point res[][];
		res = new Point[N][];
		for (int i = 0; i < N; i++) {
			res[i] = polygons(split[i].toArray(new Point[0]));
			// res[i] = split[i].toArray(new Point[0]);
		}
		while (true) {
			boolean ok = true;
			join: for (int i = 0; i < N; i++) {
				Point apoly[] = res[i];
				for (int j = i + 1; j < N; j++) {
					Point bpoly[] = res[j];
					for (int k = 0, is = apoly.length; k < is; k++) {
						Point a1 = apoly[k];
						Point a2 = apoly[(k + 1) % is];
						for (int m = 0, js = bpoly.length; m < js; m++) {
							Point b1 = bpoly[m];
							Point b2 = bpoly[(m + 1) % js];
							if (G2D.intersected(a1, a2, b1, b2)) {
								ok = false;
								--N;
								Point tmp[][] = new Point[N][];
								for (int x = 0; x < N; x++)
									tmp[x] = res[x];
								if (j < N)
									tmp[j] = res[N];
								Point joinPolys[] = new Point[is + js];
								for (int x = 0; x < is; x++)
									joinPolys[x] = apoly[x];
								for (int x = 0; x < js; x++)
									joinPolys[is + x] = bpoly[x];
								tmp[i] = polygons(joinPolys);
								res = tmp;
								break join;
							}
						}
					}
				}
			}
			if (ok)
				break;
		}
		return result(res);
	}

	double dist(Point p[]) {
		if (p.length <= 1)
			return 1;
		double res = 0;
		for (int i = 0; i < N; i++) {
			for (int j = i + 1; j < N; j++) {
				res += G2D.dist(p[i], p[j]);
			}
		}
		return res;
	}

	String[] result(Point polys[][]) {
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

	String toString(int list[]) {
		StringJoiner sj = new StringJoiner(" ");
		for (int i : list) {
			sj.add(Integer.toString(i));
		}
		return sj.toString();
	}

	class ContestXorShift extends Random {
		private static final long serialVersionUID = -8807494513400211599L;
		private long x, y, z, w;

		private void init() {
			x = 123456789;
			y = 362436069;
			z = 521288629;
			w = 88675123;
		}

		public ContestXorShift() {
			super();
			init();
			x = System.nanoTime();
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

	static class Point {
		public final int x, y;

		public Point(int x, int y) {
			this.x = x;
			this.y = y;
		}

		public boolean equals(Point other) {
			return (x == other.x && y == other.y);
		}

		public double dist() {
			return Math.sqrt(x * x + y * y);
		}

		public int hash() {
			return (x << 16) | y;
		}

		public String toString() {
			return "[ " + x + ", " + y + " ]";
		}
	}

	static class G2D {
		public static Point sub(Point p1, Point p2) {
			return new Point(p1.x - p2.x, p1.y - p2.y);
		}

		public static double norm(Point p) {
			return Math.sqrt(p.x * p.x + p.y * p.y);
		}

		public static int norm2(Point p) {
			return (p.x * p.x + p.y * p.y);
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

		public static int dist2(Point p1, Point p2) {
			return norm2(sub(p1, p2));
		}

		public static double dist(Point a, Point b, Point c) {
			if (dot(sub(b, a), sub(c, a)) < eps)
				return sub(c, a).dist();
			if (dot(sub(a, b), sub(c, b)) < eps)
				return sub(c, b).dist();
			return Math.abs(cross(sub(b, a), sub(c, a))) / sub(b, a).dist();
		}

		public static boolean intersected(Point a1, Point a2, Point b1, Point b2) {
			return ((long) cross(sub(a2, a1), sub(b1, a1)) * (long) cross(sub(a2, a1), sub(b2, a1)) < eps)
					&& ((long) cross(sub(b2, b1), sub(a1, b1)) * (long) cross(sub(b2, b1), sub(a2, b1)) < eps);
		}
	}

	class Edge {
		public Point p1, p2, vect; //vector p1 -> p2
		public double norm;

		public Edge() {
		};

		public Edge(Point p1n, Point p2n) {
			p1 = p1n;
			p2 = p2n;
			vect = G2D.sub(p2, p1);
			norm = G2D.norm(vect);
		}

		public Edge(int x1, int y1, int x2, int y2) {
			p1 = new Point(x1, y1);
			p2 = new Point(x2, y2);
			vect = G2D.sub(p2, p1);
			norm = G2D.norm(vect);
		}

		boolean eq(double a, double b) {
			return Math.abs(a - b) < 1e-9;
		}

		// ---------------------------------------------------
		public boolean intersect(Edge other) {
			//do edges "this" and "other" intersect?
			if (Math.min(p1.x, p2.x) > Math.max(other.p1.x, other.p2.x))
				return false;
			if (Math.max(p1.x, p2.x) < Math.min(other.p1.x, other.p2.x))
				return false;
			if (Math.min(p1.y, p2.y) > Math.max(other.p1.y, other.p2.y))
				return false;
			if (Math.max(p1.y, p2.y) < Math.min(other.p1.y, other.p2.y))
				return false;

			int den = other.vect.y * vect.x - other.vect.x * vect.y;
			int num1 = other.vect.x * (p1.y - other.p1.y) - other.vect.y * (p1.x - other.p1.x);
			int num2 = vect.x * (p1.y - other.p1.y) - vect.y * (p1.x - other.p1.x);

			//parallel edges
			if (den == 0) {
				if (Math.min(other.dist2(this), dist2(other)) > 0)
					return false;
				//on the same line - "not intersect" only if one of the vertices is common,
				//and the other doesn't belong to the line
				if ((this.p1 == other.p1 && eq(G2D.dist(this.p2, other.p2), this.norm + other.norm))
						|| (this.p1 == other.p2 && eq(G2D.dist(this.p2, other.p1), this.norm + other.norm))
						|| (this.p2 == other.p1 && eq(G2D.dist(this.p1, other.p2), this.norm + other.norm))
						|| (this.p2 == other.p2 && eq(G2D.dist(this.p1, other.p1), this.norm + other.norm)))
					return false;
				return true;
			}

			//common vertices
			if (this.p1 == other.p1 || this.p1 == other.p2 || this.p2 == other.p1 || this.p2 == other.p2)
				return false;

			double u1 = num1 * 1. / den;
			double u2 = num2 * 1. / den;
			if (u1 < 0 || u1 > 1 || u2 < 0 || u2 > 1)
				return false;
			return true;
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
