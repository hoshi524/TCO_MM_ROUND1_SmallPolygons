import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

public class CopyOfSmallPolygons {

	private final long startTime = System.currentTimeMillis();
	private static final boolean DEBUG = false;
	private static final boolean MEASURE_TIME = true;
	private static final int MAX_TIME = 9500;
	private static final int MAX_XY = 700;
	private static final int K = 50;
	private static final int BEAM_WIDTH_LIST[] = new int[] { 70, 62, 25, 12, 7, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
			4, 4, 4, 4, 4 };
	private static final double pai2 = Math.atan(1) * 4 * 2;
	private static final double eps = 1e-9;
	private final XorShift random = new XorShift();
	private final Timer timer = new Timer();
	private int N, NP;
	private Point ps[];
	private Map<Integer, Integer> ids;
	private Map<Integer, Long> hashTable;
	private Map<Long, Point[]> memo;

	private abstract class IntComparable implements Comparable<IntComparable> {
		int value = Integer.MAX_VALUE / 2;

		@Override
		public int compareTo(IntComparable o) {
			return value - o.value;
		}
	}

	private static final <T> T[] add(T[] src, int index, T t) {
		src = Arrays.copyOf(src, src.length + 1);
		System.arraycopy(src, index, src, index + 1, src.length - index - 1);
		src[index] = t;
		return src;
	}

	private static final <T> T[] remove(T[] src, int i) {
		src[i] = src[src.length - 1];
		src = Arrays.copyOf(src, src.length - 1);
		return src;
	}

	private Point[] polygons(Point[] t) {
		long key = 0;
		for (int i = 0, size = t.length; i < size; ++i)
			key ^= hashTable.get(t[i].hash());
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
			void setRemain(Point[] outside, Edge[] checkEdge, final Remain r) {
				for (int i = 0, size = outside.length; i < size; ++i) {
					Point a = outside[i];
					Point b = outside[(i + 1) % size];
					int v = areaDiff(a, b, r.p);
					if (r.value > v && isOK(checkEdge, new Edge(r.p, a)) && isOK(checkEdge, new Edge(r.p, b))) {
						r.value = v;
						r.t = a;
						r.u = b;
					}
				}
			}

			boolean isOK(Edge[] checkEdge, Edge e) {
				for (int i = 0, size = checkEdge.length; i < size; ++i)
					if (e.intersect(checkEdge[i]))
						return false;
				return true;
			}
		}
		Function func = new Function();

		class Polygon extends IntComparable {
			Point[] outside;
			Remain[] remain;
			Edge[] checkEdge;
			int remainIndex = -1;

			Polygon(Point[] outside, Remain[] remain, Edge[] checkEdge, int outsideArea) {
				this.outside = outside;
				this.remain = remain;
				this.checkEdge = checkEdge;
				this.value = outsideArea;
			}

			Polygon(Polygon p) {
				outside = p.outside;
				remain = new Remain[p.remain.length];
				for (int i = 0, size = remain.length; i < size; ++i)
					remain[i] = new Remain(p.remain[i]);
				checkEdge = p.checkEdge;
				value = p.value;
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
				for (int j = 0, j_size = remain.length; j < j_size; ++j) {
					Remain x = remain[j];
					Edge te0 = x.t == null ? null : new Edge(x.t, x.p);
					Edge te1 = x.u == null ? null : new Edge(x.p, x.u);
					if (te0 == null || te1 == null || (r.t == x.t && r.u == x.u) || e0.intersect(te0)
							|| e0.intersect(te1) || e1.intersect(te0) || e1.intersect(te1)) {
						x.value = Integer.MAX_VALUE / 2;
						x.t = null;
						x.u = null;
						func.setRemain(outside, checkEdge, x);
					} else if (func.isOK(checkEdge, new Edge(r.p, x.p))) {
						{
							Point a = r.t;
							Point b = r.p;
							int v = areaDiff(a, b, x.p);
							if (x.value > v && func.isOK(checkEdge, new Edge(x.p, a))
									&& func.isOK(checkEdge, new Edge(x.p, b))) {
								x.value = v;
								x.t = a;
								x.u = b;
							}
						}
						{
							Point a = r.p;
							Point b = r.u;
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
			}

			void next(int width, List<Polygon> nextPolygons, Set<Long> used) {
				Collections.sort(nextPolygons);
				int pos = width - 1;
				int limit = nextPolygons.size() >= width ? nextPolygons.get(pos--).value : Integer.MAX_VALUE / 2;
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
				for (int i = 0, size = outside.length; i < size; ++i) {
					int w = i % 64;
					long hash = hashTable.get(outside[i].hash());
					key ^= (hash << w) | (hash >> (64 - w));
					if (outside[i] == r.t) {
						outside = add(outside, i + 1, r.p);
					}
				}
				return key;
			}
		}

		Point[] outside = getOutside(t).toArray(new Point[0]);
		if (outside.length == t.length) {
			return outside;
		}
		Edge[] checkEdge = new Edge[0];
		ArrayList<Remain> remain = new ArrayList<>();
		{
			Set<Point> outsideSet = new HashSet<>(Arrays.asList(outside));
			for (int i = 0, size = t.length; i < size; ++i) {
				Point p = t[i];
				if (outsideSet.contains(p))
					continue;
				Remain r = new Remain(p);
				remain.add(r);
				func.setRemain(outside, checkEdge, r);
			}
		}
		int outsideArea = area(outside);
		int width = BEAM_WIDTH_LIST[t.length / K];
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
		res = polys.get(0).outside;
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
		hashTable = new HashMap<>();
		for (int i = 0; i < NP; ++i) {
			ps[i] = new Point(points[i * 2], points[i * 2 + 1]);
			ids.put(ps[i].hash(), i);
			hashTable.put(ps[i].hash(), random.nextLong());
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
				//				long start = System.currentTimeMillis();
				Point polys[] = polygons(tmp[i].toArray(new Point[0]));
				//				if (System.currentTimeMillis() - start >= 500) {
				//					int index = tmp[i].size() / K;
				//					--BEAM_WIDTH_LIST[index];
				//					for (int j = index; j < BEAM_WIDTH_LIST.length; ++j) {
				//						BEAM_WIDTH_LIST[j] = Math.min(BEAM_WIDTH_LIST[j], BEAM_WIDTH_LIST[index]);
				//						BEAM_WIDTH_LIST[j] = Math.max(BEAM_WIDTH_LIST[j], 5);
				//					}
				//				}
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
		//		System.out.println(Arrays.toString(BEAM_WIDTH_LIST));
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
		final int x, y;

		Point(int x, int y) {
			this.x = x;
			this.y = y;
		}

		static Point random(XorShift random) {
			return new Point(random.nextInt(MAX_XY), random.nextInt(MAX_XY));
		}

		int hash() {
			return (x << 16) | y;
		}

		public String toString() {
			return "[ " + x + ", " + y + " ]";
		}
	}

	private static final class G2D {
		static Point sub(Point p1, Point p2) {
			return new Point(p1.x - p2.x, p1.y - p2.y);
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

	private static final class Edge implements Comparable<Edge> {
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
