import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.StringJoiner;

public class CopyOfSmallPolygons {

	private static final int MAX_TIME = 9800;
	private final long startTime = System.currentTimeMillis();
	private final long endTime = startTime + MAX_TIME;
	private static final int INT_MAX = Integer.MAX_VALUE / 2;
	private static final int MAX_XY = 700;
	private static final double pai2 = Math.atan(1) * 4 * 2;
	private static final double eps = 1e-9;
	private final XorShift random = new XorShift();
	private int N, NP;
	private Point ps[];

	private final class Remain extends IntComparable {
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

		void set(Point[] outside, Edge[] checkEdge) {
			value = INT_MAX;
			for (int i = 0, size = outside.length; i < size; ++i) {
				Point a = outside[i];
				Point b = outside[(i + 1) == size ? 0 : i + 1];
				int tmp = areaDiff(a, b, p);
				if (value > tmp && new Edge(p, a).isOK(checkEdge) && new Edge(p, b).isOK(checkEdge)) {
					value = tmp;
					t = a;
					u = b;
				}
			}
		}
	}

	private final class Polygon {
		Point[] outside;
		Remain[] remain;
		Edge[] checkEdge;
		int remainIndex;

		Polygon(Point[] outside, Remain[] remain, Edge[] checkEdge) {
			this.outside = outside;
			this.remain = remain;
			this.checkEdge = checkEdge;
		}

		void nextRemain() {
			Remain r = remain[remainIndex];
			remain = remove(remain, remainIndex);
			Edge e0 = new Edge(r.t, r.p);
			Edge e1 = new Edge(r.p, r.u);
			{
				int edgeSize = checkEdge.length;
				for (int j = 0; j < edgeSize; ++j) {
					Edge e = checkEdge[j];
					if (e.p1 == r.t && e.p2 == r.u) {
						--edgeSize;
						checkEdge[j] = checkEdge[edgeSize];
						checkEdge[edgeSize] = e;
						break;
					}
				}
				checkEdge = Arrays.copyOf(checkEdge, edgeSize + 2);
				checkEdge[edgeSize] = e0;
				checkEdge[edgeSize + 1] = e1;
			}
			Arrays.sort(checkEdge);
			for (int i = 0, size = remain.length; i < size; ++i) {
				Remain x = remain[i];
				Edge te0 = x.t == null ? null : new Edge(x.t, x.p);
				Edge te1 = x.u == null ? null : new Edge(x.p, x.u);
				if (te0 == null || te1 == null || (r.t == x.t && r.u == x.u) || e0.intersect(te0) || e0.intersect(te1)
						|| e1.intersect(te0) || e1.intersect(te1)) {
					x = remain[i] = new Remain(x);
					x.t = null;
					x.u = null;
					x.set(outside, checkEdge);
				}
			}
		}

		boolean next() {
			Arrays.sort(remain);
			for (int i = 0; i < remain.length; i++) {
				Remain x = remain[i];
				if (x.t != null) {
					remainIndex = i;
					for (int j = 0, size = outside.length; j <= size; ++j) {
						if (outside[j] == x.t) {
							outside = add(outside, j + 1, x.p);
							return true;
						}
					}
				}
			}
			return false;
		}
	}

	private final Polygon polygons(Point[] t) {
		Point[] outside = getOutside(t);
		if (outside.length == t.length) {
			return new Polygon(outside, null, null);
		}
		Edge[] checkEdge = new Edge[0];
		Remain[] remain = new Remain[t.length - outside.length];
		{
			int remainIndex = 0;
			Set<Point> outsideSet = new HashSet<>(Arrays.asList(outside));
			for (Point p : t) {
				if (outsideSet.contains(p))
					continue;
				Remain r = new Remain(p);
				remain[remainIndex++] = r;
				r.set(outside, checkEdge);
			}
		}
		Polygon res = new Polygon(outside, remain, checkEdge);
		for (int i = 0; i < remain.length; ++i) {
			if (!res.next())
				return null;
			res.nextRemain();
		}
		return res;
	}

	private final int areaFunc(Point p0, Point p1) {
		return (p1.y + p0.y) * (p1.x - p0.x);
	}

	private final int areaDiff(Point p0, Point p1, Point p) {
		return -areaFunc(p0, p1) + areaFunc(p0, p) + areaFunc(p, p1);
	}

	private final int area(Point[] poly) {
		int s = areaFunc(poly[poly.length - 1], poly[0]);
		for (int i = 0, n = poly.length - 1; i < n; ++i) {
			s += areaFunc(poly[i], poly[i + 1]);
		}
		return Math.abs(s);
	}

	private final int area2(Point[] next, int start) {
		int s = 0;
		Point p = ps[start];
		while (true) {
			Point n = next[p.id];
			s += areaFunc(p, n);
			if (n.id == start)
				break;
			p = n;
		}
		return s;
	}

	private final List<Point>[] split(Point[] ps, int N) {
		Point[] x = new Point[N];
		@SuppressWarnings("unchecked")
		List<Point> res[] = new List[N];
		for (int i = 0; i < N; ++i) {
			res[i] = new ArrayList<>();
			x[i] = Point.random(random);
		}
		for (Point point : ps) {
			int t = -1;
			int dist = INT_MAX;
			for (int j = 0; j < N; ++j) {
				int tmpd = G2D.dist(x[j], point);
				if (dist > tmpd) {
					dist = tmpd;
					t = j;
				}
			}
			res[t].add(point);
		}
		for (List<Point> list : res)
			if (list.size() < 3)
				return null;
		return res;
	}

	String[] choosePolygons(int[] points, int N_) {
		this.N = N_;
		NP = points.length / 2;
		N = Math.min(N, NP / 3);
		ps = new Point[NP];
		for (int i = 0; i < NP; ++i) {
			ps[i] = new Point(i, points[i * 2], points[i * 2 + 1]);
		}

		Point res[][] = null;
		int badCount = 0;
		NG: while (true) {
			if (res == null) {
				++badCount;
				if (badCount > 40) {
					badCount = 0;
					--N;
				}
			}
			List<Point> tmp[] = split(ps, N);
			if (tmp == null)
				continue NG;
			Point restmp[][] = new Point[N][];
			for (int i = 0; i < N; ++i) {
				Polygon p = polygons(tmp[i].toArray(new Point[0]));
				if (p == null || area(p.outside) == 0)
					continue NG;
				restmp[i] = p.outside;
			}
			res = restmp;
			break;
		}
		return result(SimulatedAnnealing(res));
	}

	Point[][] SimulatedAnnealing(Point[][] polygon) {
		int area[] = new int[polygon.length];
		int in[] = new int[NP];
		int psize[] = new int[polygon.length];
		Point[] next = new Point[NP];
		int score = 0;
		for (int i = 0; i < polygon.length; ++i) {
			area[i] = area(polygon[i]);
			score += area[i];
			psize[i] = polygon[i].length;
			for (int j = 0; j < polygon[i].length; ++j) {
				in[polygon[i][j].id] = i;
				next[polygon[i][j].id] = polygon[i][j + 1 == polygon[i].length ? 0 : j + 1];
			}
		}
		int bestScore = score;
		Point[] best = Arrays.copyOf(next, next.length);
		long remainTime = 0;
		NG: for (int turn = 0;; ++turn) {
			if ((turn & 0xffff) == 0) {
				remainTime = endTime - System.currentTimeMillis();
				if (remainTime < 0)
					break;
			}

			int id = random.nextInt(NP);
			int removeI = in[id];
			if (psize[removeI] == 3)
				continue NG;
			Point p1 = ps[id], p2 = next[id], p3 = next[p2.id];
			int removeArea = areaDiff(p1, p3, p2);
			if (area[removeI] - removeArea == 0) {
				continue NG;
			}
			boolean rev0 = area[removeI] - removeArea < 0;

			int idt = random.nextInt(NP);
			while (p1.id == idt || p2.id == idt)
				idt = random.nextInt(NP);
			int addI = in[idt];
			Point mp1 = ps[idt], mp2 = next[idt];

			int addArea = areaDiff(mp1, mp2, p2);
			if (area[addI] + addArea == 0) {
				continue NG;
			}

			boolean rev1 = area[addI] + addArea < 0;
			if (rev0) {
				removeArea = -removeArea + area[removeI] + area[removeI];
				if (addI == removeI)
					addArea *= -1;
			}
			if (rev1) {
				addArea = -addArea - area[addI] - area[addI];
				if (addI == removeI)
					removeArea *= -1;
			}

			int diff = addArea - removeArea;
			if (diff * MAX_TIME > bestScore * remainTime || (diff > 0 && remainTime < random.nextInt(MAX_TIME)))
				continue NG;

			if ((p1 != mp1 && p3 != mp1 && cross(mp1, p2, p1, p3))
					|| (p1 != mp2 && p3 != mp2 && cross(p2, mp2, p1, p3)))
				continue NG;
			for (int i = 0; i < NP; ++i) {
				Point a = ps[i];
				Point b = next[i];
				if (p2 == a || p2 == b)
					continue;
				if ((a != mp1 && b != mp1 && cross(a, b, mp1, p2)) || (a != mp2 && b != mp2 && cross(a, b, p2, mp2))
						|| (a != p1 && b != p1 && a != p3 && b != p3 && cross(a, b, p1, p3)))
					continue NG;
			}

			in[p2.id] = addI;
			score += diff;
			area[removeI] -= removeArea;
			area[addI] += addArea;
			next[mp1.id] = p2;
			next[p2.id] = mp2;
			next[p1.id] = p3;
			--psize[removeI];
			++psize[addI];
			if (rev0) {
				Point x = p1, prev = null;
				while (true) {
					Point n = next[x.id];
					next[x.id] = prev;
					prev = x;
					x = n;
					if (x == null)
						break;
				}
			}
			if (rev1 && (!rev0 || removeI != addI)) {
				Point x = p2, prev = null;
				while (true) {
					Point n = next[x.id];
					next[x.id] = prev;
					prev = x;
					x = n;
					if (x == null)
						break;
				}
			}
			//			{
			//				// test
			//				for (int i = 0; i < NP; ++i) {
			//					if (area[in[i]] != area2(next, i)) {
			//						throw new RuntimeException();
			//					}
			//				}
			//			}
			if (bestScore > score) {
				bestScore = score;
				best = Arrays.copyOf(next, next.length);
			}
		}

		ArrayList<Point[]> res = new ArrayList<>();
		boolean used[] = new boolean[NP];
		for (int i = 0; i < NP; ++i) {
			if (!used[i]) {
				ArrayList<Point> p = new ArrayList<>();
				Point x = ps[i];
				while (true) {
					p.add(x);
					used[x.id] = true;
					x = best[x.id];
					if (used[x.id])
						break;
				}
				res.add(p.toArray(new Point[0]));
			}
		}
		return res.toArray(new Point[0][]);
	}

	private static int triarea(Point a, Point b, Point c) {
		int dx1 = b.x - a.x;
		int dy1 = b.y - a.y;
		int dx2 = c.x - a.x;
		int dy2 = c.y - a.y;
		return dx1 * dy2 - dx2 * dy1;
	}

	private static int ccw(Point a, Point b, Point c) {
		return Integer.signum(triarea(a, b, c));
	}

	private static boolean cross(Point p1, Point p2, Point p3, Point p4) {
		return ccw(p1, p2, p3) * ccw(p1, p2, p4) <= 0 && ccw(p3, p4, p1) * ccw(p3, p4, p2) <= 0;
	}

	private final String[] result(Point polys[][]) {
		String res[] = new String[polys.length];
		for (int i = 0; i < polys.length; ++i) {
			StringJoiner joiner = new StringJoiner(" ");
			for (Point p : polys[i])
				joiner.add(Integer.toString(p.id));
			res[i] = joiner.toString();
		}
		return res;
	}

	private static final class Point {
		final int id, x, y;

		Point(int id, int x, int y) {
			this.id = id;
			this.x = x;
			this.y = y;
		}

		static Point random(XorShift random) {
			return new Point(-1, random.nextInt(MAX_XY), random.nextInt(MAX_XY));
		}

		public String toString() {
			return "[ " + x + ", " + y + " ]";
		}
	}

	private static final class G2D {
		static Point sub(Point p1, Point p2) {
			return new Point(-1, p1.x - p2.x, p1.y - p2.y);
		}

		static int norm(int x, int y) {
			return x * x + y * y;
		}

		static int dot(Point p1, Point p2) {
			return p1.x * p2.x + p1.y * p2.y;
		}

		static int cross(Point p1, Point p2) {
			return p1.x * p2.y - p1.y * p2.x;
		}

		static int dist(Point p1, Point p2) {
			return norm(p1.x - p2.x, p1.y - p2.y);
		}
	}

	private final class Edge implements Comparable<Edge> {
		Point p1, p2, vect; //vector p1 -> p2
		int norm;

		Edge(Point p1n, Point p2n) {
			p1 = p1n;
			p2 = p2n;
			vect = G2D.sub(p2, p1);
			norm = G2D.norm(vect.x, vect.y);
		}

		boolean intersect(Edge other) {
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
				//on the same line - "not intersect" only if one of the vertices is common,
				//and the other doesn't belong to the line
				int sum = norm + other.norm;
				if ((p1 == other.p1 && G2D.dist(p2, other.p2) == sum)
						|| (p1 == other.p2 && G2D.dist(p2, other.p1) == sum)
						|| (p2 == other.p1 && G2D.dist(p1, other.p2) == sum)
						|| (p2 == other.p2 && G2D.dist(p1, other.p1) == sum)) {
					return false;
				}
				return dist(other.p1) == 0 || dist(other.p2) == 0;
			}
			//common vertices
			if (p1 == other.p1 || p1 == other.p2 || p2 == other.p1 || p2 == other.p2) {
				return false;
			}

			int mx = p1.x - other.p1.x;
			int my = p1.y - other.p1.y;
			int u1 = other.vect.x * my - other.vect.y * mx;
			int u2 = vect.x * my - vect.y * mx;
			if ((den < 0 && (u1 > 0 || u1 < den || u2 > 0 || u2 < den) || (den > 0 && (u1 < 0 || u1 > den || u2 < 0 || u2 > den)))) {
				return false;
			}
			return true;
		}

		// ---------------------------------------------------
		int dist(Point p) {
			//distance from p to the edge
			if (G2D.dot(vect, G2D.sub(p, p1)) <= 0)
				return G2D.dist(p, p1); //from p to p1
			if (G2D.dot(vect, G2D.sub(p, p2)) >= 0)
				return G2D.dist(p, p2); //from p to p2
			// distance to the line itself
			return Math.abs(-vect.y * p.x + vect.x * p.y + p1.x * p2.y - p1.y * p2.x);
		}

		@Override
		public int compareTo(Edge o) {
			return Integer.compare(o.norm, norm);
		}

		boolean isOK(Edge[] checkEdge) {
			for (Edge ce : checkEdge)
				if (intersect(ce))
					return false;
			return true;
		}
	}

	private final double angle(Point a, Point b, Point c) {
		Point v1 = G2D.sub(b, a);
		Point v2 = G2D.sub(b, c);
		return Math.atan2(G2D.cross(v1, v2), G2D.dot(v1, v2));
	}

	private final double angle2(Point a, Point b, Point c) {
		double x = angle(a, b, c);
		if (x < 0) {
			x = pai2 + x;
		}
		return x;
	}

	private final Point[] getOutside(Point[] t) {
		Point init = t[0];
		for (int i = 1, size = t.length; i < size; ++i)
			if (init.y > t[i].y)
				init = t[i];
		Point p1 = new Point(-1, init.x, init.y - 1);
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
		return outside.toArray(new Point[0]);
	}

	private final class XorShift {
		int x = 123456789;
		int y = 362436069;
		int z = 521288629;
		int w = 88675123;

		int nextInt(int n) {
			final int r = nextInt() % n;
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
	}

	private abstract class IntComparable implements Comparable<IntComparable> {
		int value = INT_MAX;

		@Override
		public int compareTo(IntComparable o) {
			return value - o.value;
		}
	}

	private final <T> T[] add(T[] src, int index, T t) {
		src = Arrays.copyOf(src, src.length + 1);
		System.arraycopy(src, index, src, index + 1, src.length - index - 1);
		src[index] = t;
		return src;
	}

	private final <T> T[] remove(T[] src, int index) {
		T[] res = Arrays.copyOf(src, src.length - 1);
		System.arraycopy(src, index + 1, res, index, src.length - index - 1);
		return res;
	}
}
