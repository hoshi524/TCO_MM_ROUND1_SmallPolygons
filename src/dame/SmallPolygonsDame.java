package dame;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

public class SmallPolygonsDame {

	private static final int MAX_TIME = 9500;
	private final long endTime = System.currentTimeMillis() + MAX_TIME;
	private static final int INT_MAX = Integer.MAX_VALUE / 2;
	private static final int MAX_XY = 700;
	private static final int K = 50;
	private static final int BEAM_WIDTH_LIST[] = new int[] { 50, 20, 8, 5 };
	private static final int TN = 3;
	private static final double pai2 = Math.atan(1) * 4 * 2;
	private static final double eps = 1e-9;
	private final XorShift random = new XorShift();
	private int N, NP;
	private Point ps[];
	private long[] hashTable;
	private Map<Long, Polygon> memo;

	private final class Remain extends IntComparable {
		final Point p;
		Point t = null, u = null;
		byte badEdges[];

		Remain(Point p, int n) {
			this.p = p;
			badEdges = new byte[n];
		}

		Remain(Remain r) {
			p = r.p;
			t = r.t;
			u = r.u;
			value = r.value;
			badEdges = Arrays.copyOf(r.badEdges, r.badEdges.length + 1);
		}

		void set(Edge[] edges) {
			value = INT_MAX;
			t = null;
			u = null;
			for (int i = 0, size = edges.length; i < size; ++i) {
				if (badEdges[i] == 0) {
					Edge e = edges[i];
					int v = areaDiff(e.p1, e.p2, p);
					if (value > v) {
						value = v;
						t = e.p1;
						u = e.p2;
					}
				}
			}
		}
	}

	private final class Polygon extends IntComparable {
		Point[] outside;
		Remain[] remain;
		Edge[] checkEdge;
		Edge[] edges;
		int remainIndex;

		Polygon(Point[] outside, Remain[] remain, Edge[] checkEdge, int outsideArea) {
			this.outside = outside;
			this.remain = remain;
			this.checkEdge = checkEdge;
			this.value = outsideArea;
			edges = new Edge[outside.length];
			for (int i = 0, size = outside.length; i < size; ++i) {
				edges[i] = new Edge(outside[i], outside[(i + 1) % size]);
			}
			if (remain != null)
				for (Remain r : remain)
					r.set(edges);
		}

		Polygon(Polygon p) {
			outside = p.outside;
			remain = p.remain;
			checkEdge = p.checkEdge;
			value = p.value;
			edges = p.edges;
		}

		void nextRemain() {
			Remain r = remain[remainIndex];
			remain = remove(remain, remainIndex);
			Edge e0 = new Edge(r.t, r.p);
			Edge e1 = new Edge(r.p, r.u);
			Edge delete = null;
			int deleteIndex = -1;
			for (int i = 0, size = edges.length; i < size; ++i) {
				Edge e = edges[i];
				if (e.p1 == r.t && e.p2 == r.u) {
					deleteIndex = i;
					delete = e;
					edges = add(edges, e0);
					edges[i] = e1;
					break;
				}
			}
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
			for (int i = 0, size = remain.length; i < size; ++i) {
				Remain x = remain[i] = new Remain(remain[i]);
				x.value = INT_MAX;
				x.t = null;
				x.u = null;
				for (int j = 0, j_size = edges.length; j < j_size; ++j) {
					Edge e = edges[j];
					Edge t0 = new Edge(x.p, e.p1);
					Edge t1 = new Edge(x.p, e.p2);
					if (deleteIndex == j || j_size - 1 == j) {
						x.badEdges[j] = 0;
						for (Edge check : checkEdge)
							if (t0.intersect(check) || t1.intersect(check))
								++x.badEdges[j];
					} else {
						if (t0.intersect(delete) || t1.intersect(delete))
							--x.badEdges[j];
						if (t0.intersect(e0) || t1.intersect(e0))
							++x.badEdges[j];
						if (t0.intersect(e1) || t1.intersect(e1))
							++x.badEdges[j];
					}
					if (x.badEdges[j] == 0) {
						int v = areaDiff(e.p1, e.p2, x.p);
						if (x.value > v) {
							x.value = v;
							x.t = e.p1;
							x.u = e.p2;
						}
					}
				}
			}
		}

		void next(int width, List<Polygon> nextPolygons, Set<Long> used) {
			Collections.sort(nextPolygons);
			int pos = width - 1;
			int limit = nextPolygons.size() >= width ? nextPolygons.get(pos--).value : INT_MAX;
			Arrays.sort(remain);
			for (int j = 0, j_size = Math.min(width, remain.length); j < j_size; ++j) {
				Remain x = remain[j];
				if (limit <= value + x.value)
					return;
				if (x.t != null) {
					Polygon nextPolygon = new Polygon(this);
					long key = nextPolygon.step(j);
					if (!used.contains(key)) {
						nextPolygons.add(nextPolygon);
						used.add(key);
						if (nextPolygons.size() < width || pos == 0) {
						} else if (nextPolygons.get(pos).value > nextPolygon.value)
							limit = nextPolygons.get(pos--).value;
						else
							return;
					}
				}
			}
		}

		long step(int index) {
			remainIndex = index;
			Remain r = remain[index];
			value += r.value;
			long key = 0;
			for (int i = 0, size = outside.length; i <= size; ++i) {
				int w = i % 64;
				long hash = hashTable[outside[i].id];
				key ^= (hash << w) | (hash >>> (64 - w));
				if (outside[i] == r.t) {
					outside = add(outside, i + 1, r.p);
				}
			}
			return key;
		}
	}

	boolean contains(Point[] polygon, Point p) {
		boolean in = false;
		for (int i = 0, size = polygon.length; i < size; ++i) {
			Point a = G2D.sub(polygon[i], p), b = G2D.sub(polygon[(i + 1) % size], p);
			if (a.x > b.x) {
				Point tmp = a;
				a = b;
				b = tmp;
			}
			if (a.x <= 0 && 0 < b.x && G2D.cross(a, b) < 0)
				in = !in;
			if (G2D.cross(a, b) == 0 && G2D.dot(a, b) <= 0)
				return true;
		}
		return in;
	}

	boolean convex_contains(Point[] P, Point p) {
		int n = P.length;
		int sumx = P[0].x + P[n / 3].x + P[2 * n / 3].x;
		int sumy = P[0].y + P[n / 3].y + P[2 * n / 3].y;
		Point g = new Point(-1, Math.round((float) sumx / 3), Math.round((float) sumy / 3)); // inner-point
		int a = 0, b = n;
		while (a + 1 < b) { // invariant: c is in fan g-P[a]-P[b]
			int c = (a + b) / 2;
			if (G2D.cross(G2D.sub(P[a], g), G2D.sub(P[c], g)) > 0) { // angle < 180 deg
				if (G2D.cross(G2D.sub(P[a], g), G2D.sub(p, g)) > 0 && G2D.cross(G2D.sub(P[c], g), G2D.sub(p, g)) < 0)
					b = c;
				else
					a = c;
			} else {
				if (G2D.cross(G2D.sub(P[a], g), G2D.sub(p, g)) < 0 && G2D.cross(G2D.sub(P[c], g), G2D.sub(p, g)) > 0)
					a = c;
				else
					b = c;
			}
		}
		b %= n;
		if (G2D.cross(G2D.sub(P[a], p), G2D.sub(P[b], p)) < 0)
			return false;
		if (G2D.cross(G2D.sub(P[a], p), G2D.sub(P[b], p)) > 0)
			return true;
		return true;
	}

	private final Polygon polygons(Point[] t) {
		return polygons(t, new Edge[0]);
	}

	private final Polygon polygons(Point[] t, Edge[] checkEdge) {
		long key = 0;
		for (Point p : t)
			key ^= hashTable[p.id];
		Polygon res = memo.get(key);
		if (res != null) {
			return res;
		}
		Point[] outside = getOutside(t);
		if (outside.length == t.length) {
			return new Polygon(outside, null, null, area(outside));
		}
		ArrayList<Remain> remain = new ArrayList<>(t.length);
		{
			Set<Point> outsideSet = new HashSet<>(Arrays.asList(outside));
			for (Point p : t) {
				if (outsideSet.contains(p))
					continue;
				Remain r = new Remain(p, outside.length);
				remain.add(r);
			}
		}
		int outsideArea = area(outside);
		int widthIndex = t.length / K;
		int width;
		if (widthIndex < BEAM_WIDTH_LIST.length) {
			width = BEAM_WIDTH_LIST[widthIndex];
		} else {
			width = 2;
		}
		List<Polygon> polys = new ArrayList<>(width * width / 2);
		List<Polygon> next = new ArrayList<>(width * width / 2);
		Set<Long> used = new HashSet<>();
		new Polygon(outside, remain.toArray(new Remain[0]), checkEdge, outsideArea).next(width, polys, used);
		for (int i = 0, size = remain.size() - 1; i < size; ++i) {
			Collections.sort(polys);
			used.clear();
			next.clear();
			for (int j = 0, j_size = Math.min(width, polys.size()); j < j_size; ++j) {
				Polygon p = polys.get(j);
				p.nextRemain();
				p.next(width, next, used);
			}
			if (next.isEmpty()) {
				return null;
			}
			{
				List<Polygon> tmp = polys;
				polys = next;
				next = tmp;
			}
		}
		Collections.sort(polys);
		if (polys.isEmpty()) {
			return null;
		}
		res = polys.get(0);
		memo.put(key, res);
		return res;
	}

	private final Point[][] calcPolygon(Point[] ps, int N, int min, Edge[] checkEdge) {
		long endTime = Math.min(this.endTime, System.currentTimeMillis() + 1000);
		NG: while (true) {
			List<Point> tmp[] = split(ps, N);
			if (tmp == null)
				continue NG;

			Point res[][] = new Point[N][];
			int value = 0;
			for (int i = 0; i < N; ++i) {
				if (System.currentTimeMillis() >= endTime) {
					return null;
				}
				Polygon p = polygons(tmp[i].toArray(new Point[0]), checkEdge);
				if (p == null || p.value == 0)
					continue NG;
				value += p.value;
				if (min <= value)
					continue NG;
				res[i] = p.outside;
			}
			return res;
		}
	}

	private final int areaFunc(Point p0, Point p1) {
		return (p1.y + p0.y) * (p1.x - p0.x);
	}

	private final int areaDiff(Point p0, Point p1, Point p) {
		return -areaFunc(p0, p1) + areaFunc(p0, p) + areaFunc(p, p1);
	}

	private final int area(Point[] poly) {
		int s = 0;
		for (int i = 0, n = poly.length; i < n; ++i) {
			s += areaFunc(poly[i], poly[(i + 1) % n]);
		}
		return Math.abs(s);
	}

	private final List<Point>[] split(Point[] ps, int N) {
		if (N <= 0)
			throw new RuntimeException();
		Point[] x = new Point[N];
		@SuppressWarnings("unchecked")
		List<Point> res[] = new List[N];
		for (int i = 0; i < N; ++i) {
			res[i] = new ArrayList<>();
			x[i] = Point.random(random);
		}
		for (Point point : ps) {
			int t = -1;
			double dist = Double.MAX_VALUE / 2;
			for (int j = 0; j < N; ++j) {
				double tmpd = G2D.dist(x[j], point);
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

	public String[] choosePolygons(int[] points, int N_) {
		this.N = N_;
		NP = points.length / 2;
		N = Math.min(N, NP / 3);
		ps = new Point[NP];
		memo = new HashMap<>();
		hashTable = new long[NP];
		for (int i = 0; i < NP; ++i) {
			ps[i] = new Point(i, points[i * 2], points[i * 2 + 1]);
			hashTable[i] = random.nextLong();
		}

		Point res[][] = null;
		{
			int min = INT_MAX;
			int badCount = 0;
			long prevtime = System.currentTimeMillis(), onetime = 0;
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
				{
					long now = System.currentTimeMillis();
					onetime = Math.max(onetime, now - prevtime);
					if (now + onetime >= endTime) {
						break;
					}
					prevtime = now;
				}

				Point restmp[][] = new Point[N][];
				int value = 0;
				for (int i = 0; i < N; ++i) {
					Polygon p = polygons(tmp[i].toArray(new Point[0]));
					if (p == null || p.value == 0) {
						continue NG;
					}
					value += p.value;
					if (min <= value)
						continue NG;
					restmp[i] = p.outside;
				}
				min = value;
				res = restmp;
				if (N > TN)
					break;
			}
		}
		if (N <= TN)
			return result(res);
		class Piar {
			double value;
			Point p[];

			Piar(Point p[]) {
				update(p);
			}

			void update(Point p[]) {
				this.p = p;
				value = (double) area(p) / p.length;
			}
		}
		Piar pl[] = new Piar[res.length];
		for (int i = 0, size = res.length; i < size; ++i) {
			pl[i] = new Piar(res[i]);
		}
		int worst = 0, numWorst = 0, timeup = 0;
		long prevtime = System.currentTimeMillis(), onetime = 0;
		end: while (true) {
			Arrays.sort(pl, new Comparator<Piar>() {
				@Override
				public int compare(Piar o1, Piar o2) {
					return Double.compare(o2.value, o1.value);
				}
			});
			retry: for (int pi = 0; pi < pl.length; ++pi) {
				{
					long now = System.currentTimeMillis();
					onetime = Math.min(Math.max(onetime, now - prevtime), 1000);
					if (now + onetime >= endTime) {
						break end;
					}
					prevtime = now;
				}
				Set<Piar> use = new HashSet<>();
				use.add(pl[pi]);
				for (int i = 0; i < TN - 1; i++) {
					int sumx = 0, sumy = 0, sump = 0;
					for (Piar piar : use) {
						sump += piar.p.length;
						for (Point point : piar.p) {
							sumx += point.x;
							sumy += point.y;
						}
					}
					Point center = new Point(-1, Math.round((float) sumx / sump), Math.round((float) sumy / sump));
					Piar t = null;
					double minDist = Double.MAX_VALUE;
					for (Piar piar : pl)
						if (!use.contains(piar)) {
							for (Point point : piar.p) {
								double dist = G2D.dist(center, point);
								if (minDist > dist) {
									minDist = dist;
									t = piar;
								}
							}
						}
					use.add(t);
				}
				Piar[] targetPiar = use.toArray(new Piar[0]);
				int nowArea = 0;
				int pointNum = 0;
				for (Piar piar : targetPiar) {
					nowArea += area(piar.p);
					pointNum += piar.p.length;
				}
				Point targetPoint[] = new Point[pointNum];
				int minx = Integer.MAX_VALUE, maxx = Integer.MIN_VALUE;
				int miny = Integer.MAX_VALUE, maxy = Integer.MIN_VALUE;
				{
					int numTp = 0;
					for (Piar piar : targetPiar) {
						for (Point point : piar.p) {
							targetPoint[numTp++] = point;
							minx = Math.min(minx, point.x);
							maxx = Math.max(maxx, point.x);
							miny = Math.min(miny, point.y);
							maxy = Math.max(maxy, point.y);
						}
					}
				}
				/**
				 * 上がると思ったら上がらなかった
				 */
				List<Edge> checkEdges = new ArrayList<>();
				{
					Point[] outside = getOutside(targetPoint);
					for (Piar piar : pl) {
						if (!use.contains(piar)) {
							Point list[] = piar.p;
							for (int i = 0, size = list.length; i < size; ++i) {
								Point p = list[i];
								if (minx <= p.x && p.x <= maxx && miny <= p.y && p.y <= maxy && contains(outside, p)) {
									checkEdges.add(new Edge(p, list[(i + 1) % size]));
									checkEdges.add(new Edge(p, list[(i + size - 1) % size]));
								}
							}
						}
					}
				}
				Point[][] update = calcPolygon(targetPoint, TN, nowArea, checkEdges.toArray(new Edge[0]));
				if (update == null) {
					timeup++;
					continue retry;
				}
				++numWorst;
				for (Piar p : pl) {
					if (use.contains(p))
						continue;
					Point[] poly1 = p.p;
					for (int i = 0; i < poly1.length; ++i) {
						Edge edge = new Edge(poly1[i], poly1[(i + 1) % poly1.length]);
						for (Point[] poly2 : update) {
							for (int j = 0; j < poly2.length; ++j) {
								if (edge.intersect(new Edge(poly2[j], poly2[(j + 1) % poly2.length]))) {
									++worst;
									continue retry;
								}
							}
						}
					}
				}
				for (int i = 0; i < targetPiar.length; ++i) {
					targetPiar[i].update(update[i]);
				}
				break;
			}
		}
		for (int i = 0; i < pl.length; ++i) {
			res[i] = pl[i].p;
		}
		// System.out.println(getClass().getName() + " worst : " + worst + " / " + numWorst + "   timeup? : " + timeup);
		return result(res);
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

		static double norm(int x, int y) {
			return Math.sqrt(x * x + y * y);
		}

		static int dot(Point p1, Point p2) {
			return p1.x * p2.x + p1.y * p2.y;
		}

		static int cross(Point p1, Point p2) {
			return p1.x * p2.y - p1.y * p2.x;
		}

		static double dist(Point p1, Point p2) {
			return norm(p1.x - p2.x, p1.y - p2.y);
		}
	}

	private final class Edge implements Comparable<Edge> {
		Point p1, p2, vect; //vector p1 -> p2
		double norm;

		Edge(Point p1n, Point p2n) {
			p1 = p1n;
			p2 = p2n;
			vect = G2D.sub(p2, p1);
			norm = G2D.norm(vect.x, vect.y);
		}

		boolean eq(double a, double b) {
			return Math.abs(a - b) < eps;
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
				if ((p1 == other.p1 && eq(G2D.dist(p2, other.p2), norm + other.norm))
						|| (p1 == other.p2 && eq(G2D.dist(p2, other.p1), norm + other.norm))
						|| (p2 == other.p1 && eq(G2D.dist(p1, other.p2), norm + other.norm))
						|| (p2 == other.p2 && eq(G2D.dist(p1, other.p1), norm + other.norm))) {
					return false;
				}
				return dist(other.p1) < eps || dist(other.p2) < eps;
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
		double dist(Point p) {
			//distance from p to the edge
			if (G2D.dot(vect, G2D.sub(p, p1)) <= 0)
				return G2D.dist(p, p1); //from p to p1
			if (G2D.dot(vect, G2D.sub(p, p2)) >= 0)
				return G2D.dist(p, p2); //from p to p2
			//distance to the line itself
			return Math.abs(-vect.y * p.x + vect.x * p.y + p1.x * p2.y - p1.y * p2.x) / norm;
		}

		@Override
		public int compareTo(Edge o) {
			return Double.compare(o.norm, norm);
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

		long nextLong() {
			return ((long) nextInt() << 32) | nextInt();
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

	private final <T> T[] add(T[] src, T t) {
		src = Arrays.copyOf(src, src.length + 1);
		src[src.length - 1] = t;
		return src;
	}

	private final <T> T[] remove(T[] src, int i) {
		T[] res = Arrays.copyOf(src, src.length - 1);
		if (i == src.length - 1)
			return res;
		res[i] = src[src.length - 1];
		return res;
	}
}
