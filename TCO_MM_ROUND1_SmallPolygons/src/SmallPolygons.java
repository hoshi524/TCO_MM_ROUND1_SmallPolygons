import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.StringJoiner;

public class SmallPolygons {
	@SuppressWarnings("unchecked")
	String[] choosePolygons(int[] points, int N) {
		int NP = points.length / 2;
		List<Integer> polys[] = new List[N];
		for (int i = 0; i < N; i++)
			polys[i] = new ArrayList<>();
		Random random = new ContestXorShift();
		boolean used[] = new boolean[NP];
		for (int i = 0; i < NP; i++) {
			int min = Integer.MAX_VALUE;
			int id = -1;
			while (true) {
				id = random.nextInt(NP);
				if (!used[id]) {
					used[id] = true;
					break;
				}
			}
			for (List<Integer> list : polys) {
				min = Math.min(min, list.size());
			}
			List<Integer> t = new ArrayList<>();
			for (int j = 0; j < polys.length; j++) {
				if (polys[j].size() == min)
					t.add(j);
			}
			polys[t.get(random.nextInt(t.size()))].add(id);
		}
		return result(polys);
	}

	String[] result(List<Integer> polys[]) {
		String res[] = new String[polys.length];
		for (int i = 0; i < polys.length; i++) {
			res[i] = toString(polys[i].toArray(new Integer[0]));
		}
		return res;
	}

	String toString(Integer list[]) {
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

}
