import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;

public class SmallPolygons {

	Random random = new ContestXorShift();
	int N, NP, points[];
	Point ps[];

	String[] choosePolygons(int[] points, int N) {
		this.N = N;
		this.points = points;
		NP = points.length / 2;
		ps = new Point[NP];
		for (int i = 0; i < NP; i++) {
			ps[i] = new Point(i, points[i * 2], points[i * 2 + 1]);
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
		List<Point> res[] = new List[N];
		Set<Integer> used = new HashSet<>();
		for (int i = 0; i < N; i++) {
			res[i] = new ArrayList<>();
			res[i].add(best[i]);
			used.add(best[i].id);
		}
		for (Point p : ps) {
			if (used.contains(p.id))
				continue;
			List<Point> t = null;
			double dist = Double.MAX_VALUE / 2;
			for (int i = 0; i < N; i++) {
				double tmp = G2D.dist(res[i].get(0), p);
				if (dist > tmp) {
					dist = tmp;
					t = res[i];
				}
			}
			t.add(p);
		}

		return result(res);
	}

	double dist(Point p[]) {
		double res = 0;
		for (int i = 0; i < N; i++) {
			for (int j = i + 1; j < N; j++) {
				res += G2D.dist(p[i], p[j]);
			}
		}
		return res;
	}

	String[] result(List<Point> polys[]) {
		String res[] = new String[polys.length];
		for (int i = 0; i < polys.length; i++) {
			int n = polys[i].size();
			int list[] = new int[n];
			for (int j = 0; j < n; j++) {
				list[j] = polys[i].get(j).id;
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
		public final int id, x, y;

		public Point(int id, int x, int y) {
			this.id = id;
			this.x = x;
			this.y = y;
		}

		public boolean equals(Point other) {
			return (x == other.x && y == other.y);
		}
	}

	static class G2D {
		public static Point substr(Point p1, Point p2) {
			return new Point(-1, p1.x - p2.x, p1.y - p2.y);
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
			return norm(substr(p1, p2));
		}

		public static int dist2(Point p1, Point p2) {
			return norm2(substr(p1, p2));
		}
	}

	class Edge {
		public Point p1, p2, vect; //vector p1 -> p2
		public double norm;

		public Edge(Point p1n, Point p2n) {
			p1 = p1n;
			p2 = p2n;
			vect = G2D.substr(p2, p1);
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
			if (G2D.dot(vect, G2D.substr(p, p1)) <= 0)
				return G2D.dist(p, p1); //from p to p1
			if (G2D.dot(vect, G2D.substr(p, p2)) >= 0)
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
