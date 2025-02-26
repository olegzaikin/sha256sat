__in bit M[16][32];

__out bit Hash[8][32];

bit A[32] = 0x6A09E667;
bit B[32] = 0xBB67AE85;
bit C[32] = 0x3C6EF372;
bit D[32] = 0xA54FF53A;
bit E[32] = 0x510E527F;
bit F[32] = 0x9B05688C;
bit G[32] = 0x1F83D9AB;
bit H[32] = 0x5BE0CD19;

bit W[19][32];

bit K[19][32];

void init()
{
	K[0]  = 0x428A2F98;
	K[1]  = 0x71374491;
	K[2]  = 0xB5C0FBCF;
	K[3]  = 0xE9B5DBA5;
	K[4]  = 0x3956C25B;
	K[5]  = 0x59F111F1;
	K[6]  = 0x923F82A4;
	K[7]  = 0xAB1C5ED5;
	K[8]  = 0xD807AA98;
	K[9]  = 0x12835B01;
	K[10] = 0x243185BE;
	K[11] = 0x550C7DC3;
	K[12] = 0x72BE5D74;
	K[13] = 0x80DEB1FE;
	K[14] = 0x9BDC06A7;
	K[15] = 0xC19BF174;
	K[16] = 0xE49B69C1;
	K[17] = 0xEFBE4786;
	K[18] = 0x0FC19DC6;
}

void main()
{
	init();

	int i;
	for(i = 0; i < 16; i = i + 1)
	{
		W[i] = M[i];
	}

	for(i = 16; i < 19; i = i + 1)
	{
		__mem bit s0[32] = (W[i-15] >>> 7) ^ (W[i-15] >>> 18) ^ (W[i-15] >> 3);
		__mem bit s1[32] = (W[i-2] >>> 17) ^ (W[i-2] >>> 19) ^ (W[i-2] >> 10);
		W[i] = sum(W[i-16],sum(s0, sum(W[i-7], s1, 32), 32),32);
	}

	bit a[32] = A;
	bit b[32] = B;
	bit c[32] = C;
	bit d[32] = D;
	bit e[32] = E;
	bit f[32] = F;
	bit g[32] = G;
	bit h[32] = H;

	for(i = 0; i < 19; i = i + 1)
	{
		__mem bit s0[32] = (a >>> 2) ^ (a >>> 13) ^ (a >>> 22);
		__mem bit ma[32] = (a & b) ^ (a & c) ^ (b & c);
		bit t2[32] = sum(s0, ma, 32);
		__mem bit s1[32] = (e >>> 6) ^ (e >>> 11) ^ (e >>> 25);
		__mem bit ch[32] = (e & f) ^ (!e & g);
		bit t1[32] = sum(h, sum(s1, sum(ch, sum(K[i], W[i], 32), 32), 32), 32);

		h = g;
		g = f;
		f = e;
		e = sum(d, t1, 32);
		d = c;
		c = b;
		b = a;
		a = sum(t1, t2, 32);
	}

	A = sum(A, a, 32);
	B = sum(B, b, 32);
	C = sum(C, c, 32);
	D = sum(D, d, 32);
	E = sum(E, e, 32);
	F = sum(F, f, 32);
	G = sum(G, g, 32);
	H = sum(H, h, 32);

	Hash[0] = A;
	Hash[1] = B;
	Hash[2] = C;
	Hash[3] = D;
	Hash[4] = E;
	Hash[5] = F;
	Hash[6] = G;
	Hash[7] = H;

	assert (!Hash[0]);
	assert (!Hash[1]);
	assert (!Hash[2]);
	assert (!Hash[3]);
	assert (!Hash[4]);
	assert (!Hash[5]);
	assert (!Hash[6]);
	assert (!Hash[7]);
}
