import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Random;
class ByteComparator implements Comparator<byte[]> {
	  @Override
	public int compare(byte[] a, byte[] b) {
	    int n = Math.min(a.length, b.length);
	    for (int i = 0; i < n; ++i) {
	      int delta = a[i] - b[i];   
	      if (delta != 0) { return delta; }
	    }
	    return 0;
	  }
}
public class APSI {
	final static int qLength = 160;
	final static int pLength = 1024;
    static BigInteger[] sigmas;
	static SecureRandom rnd = null;
	static MessageDigest md = null;
   
	static BigInteger p, q, g, N, d, e, Y, Rs, Rci;
	static int numberOfServerFriends, numberOfClientFriends;

	public static void setNumberOfClientFriends(int number) {
		numberOfClientFriends = number;
	}

	public static void setNumberOfServerFriends(int number) {
		numberOfServerFriends = number;
	}

    public void APSI_call() {
		init();
	}

    public static BigInteger lcm(BigInteger s, BigInteger s1) 
    { 

        BigInteger mul = s.multiply(s1); 
        BigInteger gcd = s.gcd(s1); 
        BigInteger lcm = mul.divide(gcd); 
        return lcm; 
    } 

	private static void init() {
		try {
			rnd = SecureRandom.getInstance("SHA1PRNG");
		}
		catch (NoSuchAlgorithmException e) {
			System.out.println("Error: SHA1PRNG not found."+e);
		}

		try {
			md=MessageDigest.getInstance("SHA-1");
		}
		catch (Exception e) {
			System.out.println("Error: SHA-1 not found."+e);
		}

		p = new BigInteger("B10B8F96A080E01DDE92DE5EAE5D54EC52C99FBCFB06A3C69A6A9DCA52D23B616073E28675A23D189838EF1E2EE652C013ECB4AEA906112324975C3CD49B83BFACCBDD7D90C4BD7098488E9C219A73724EFFD6FAE5644738FAA31A4FF55BCCC0A151AF5F0DC8B4BD45BF37DF365C1A65E68CFDA76D4DA708DF1FB2BC2E4A4371", 16);
		g = new BigInteger("A4D1CBD5C3FD34126765A442EFB99905F8104DD258AC507FD6406CFF14266D31266FEA1E5C41564B777E690F5504F213160217B4B01B886A5E91547F9E2749F4D7FBD7D3B9A92EE1909D0D2263F80A76A6A24C087A091F531DBF0A0169B6A28AD662A4D18E73AFA32D779D5918D08BC8858F4DCEF97C2A24855E6EEB22B3B2E5", 16);
		q = new BigInteger("F518AA8781A8DF278ABA4E7D64B7CB9D49462353", 16);
        N = p.multiply(q);

        BigInteger p1 = p.subtract(new BigInteger("1"));
        BigInteger q1 = p.subtract(new BigInteger("1"));
        BigInteger lamdba = lcm(p1,q1);

        e = new BigInteger("10001",16); 
        d = e.modInverse(lamdba);
        d = new BigInteger(d+"",16); 
	}

    private static BigInteger H(byte[] v) { 
    	md.reset();
    	md.update(v);
    	byte[] hash=md.digest();
    	BigInteger hv = new BigInteger(1, hash);
    	return hv;
    }


    private static byte[] Hprime(BigInteger v) {
    	byte[] vb=v.toByteArray();
		md.reset();
		md.update(vb);
		byte[] digest=md.digest();
		byte[] buf = new byte[160/8];
        System.arraycopy(digest, 0, buf, 0, 160/8);
		return buf;
	}

    static void permute(BigInteger[] a) { 
    	List<BigInteger> list = new ArrayList<BigInteger>(a.length);
    	for(int i=0; i<a.length; i++)
    		list.add(a[i]);
    	java.util.Collections.shuffle(list);
    	for(int i=0; i<a.length; i++)
    		a[i]=list.get(i);
    }

    private static BigInteger[] computeSigma(byte[][] c)
    {
        sigmas = new BigInteger[numberOfClientFriends];
        for(int i = 0; i < numberOfClientFriends; i++)
        {
            sigmas[i] = H(c[i]).modPow(d,N);
            
        }
        return sigmas;
    }

    private static byte[][] server_offline(byte[][] s)
    {
        byte[][] ts = new byte[numberOfServerFriends][];
        BigInteger sq = N.sqrt();
        BigInteger val = sq.divide(new BigInteger("2"));
		do {
			Rs = new BigInteger(qLength, rnd);
		} while (Rs.compareTo(val) >= 0);

        for (int i = 0; i < numberOfServerFriends; i++) {
			ts[i] = Hprime(H(s[i]).modPow(Rs.multiply(new BigInteger("2")), N));
		}

        ByteComparator myComparator = new ByteComparator();
        java.util.Arrays.sort(ts, myComparator);
        return ts;
    }

    private static BigInteger[] client_online()
    {
        BigInteger a[] = new BigInteger[numberOfClientFriends];
        BigInteger sq = N.sqrt();
        BigInteger val = sq.divide(new BigInteger("2"));
		do {
			Rci = new BigInteger(qLength, rnd);
		} while (Rci.compareTo(val) >= 0);

        BigInteger grci = g.modPow(Rci,N);
        for(int i = 0; i < numberOfClientFriends; i++)
        {
            
            a[i] = grci.multiply(sigmas[i]);
        }

        return a;
    }

    private static BigInteger[] server_online(BigInteger[] a)
    {
        BigInteger aPrime[] = new BigInteger[numberOfClientFriends];
        BigInteger twoe = e.multiply(new BigInteger("2"));
        BigInteger twoeRS = twoe.multiply(Rs); 
        Y = g.modPow(twoeRS,N);

        for(int i = 0; i < numberOfClientFriends; i++)
        {
            aPrime[i] =  a[i].modPow(twoeRS,N);
        }
        return aPrime;
    }

    private static int clientFindsMatches(BigInteger[] aPrime, byte[][] ts)
    {
        
        BigInteger YRci = Y.modPow(Rci,N);
        BigInteger inverse = YRci.modInverse(N);

        byte[][] tc = new byte[numberOfClientFriends][];
        for(int i = 0; i < numberOfClientFriends; i++)
        {
            tc[i] = Hprime(aPrime[i].multiply(inverse));
        }

        ByteComparator myComparator = new ByteComparator();
    	java.util.Arrays.sort(tc, myComparator);

       
    	int i=0; int j=0;
    	int found=0;
		while (j < numberOfServerFriends & i < numberOfClientFriends) {
    		int cmp=myComparator.compare(tc[i],ts[j]);
    		if(cmp==0){
    			i+=1;
    			j+=1;
    			found++;
    		}
    		else if(cmp<0) {
    			i+=1;
    		}
    		else {
    			j+=1;
    		}
    	}

        for(i = 0; i<numberOfClientFriends; i++)
            System.out.println("tci" + tc[i]);
         System.out.println();   
        for(i = 0; i<numberOfServerFriends; i++)
            System.out.println("tsi" + ts[i]);
		
        return found;

    }

    private static void perform(String[] serverIds, String[] clientIds) {
		
		numberOfServerFriends = serverIds.length; 
		numberOfClientFriends = clientIds.length; 

		System.out.println("numberOfServerFriends: " + numberOfServerFriends);
		System.out.println("numberOfClientFriends: " +  numberOfClientFriends);

		

		byte[][] s = new byte[numberOfServerFriends][]; 														
		byte[][] c = new byte[numberOfClientFriends][]; 

		
		byte[] C;

		for (int i = 0; i < numberOfServerFriends; i++) {
			BigInteger serverFriend = new BigInteger(serverIds[i]);
			s[i] = serverFriend.toByteArray();
            System.out.println("s[I]: " +s[i] );
            
		}
		for (int i = 0; i < numberOfClientFriends; i++) {
			BigInteger clientFriend = new BigInteger(clientIds[i]);
			c[i] = clientFriend.toByteArray();
            System.out.println("c[I]: " + c[i] );
		}
		C = new BigInteger(String.valueOf(1)).toByteArray();


		setNumberOfServerFriends(numberOfServerFriends);
		setNumberOfClientFriends(numberOfClientFriends);

		long tc1s = System.currentTimeMillis();
		BigInteger[] sigmas = computeSigma(c);
		long tc1e = System.currentTimeMillis();

        byte[][] ts = new byte[numberOfServerFriends][];
		long tc2s = System.currentTimeMillis();
		ts = server_offline(s);
		long tc2e = System.currentTimeMillis();

		long ts1s = System.currentTimeMillis();
		BigInteger[] a = client_online();
		long ts1e = System.currentTimeMillis();

        long ts2s = System.currentTimeMillis();
		BigInteger[] aPrime = server_online(a);
		long ts2e = System.currentTimeMillis();

        long tc3s = System.currentTimeMillis();
		int found = clientFindsMatches(aPrime, ts);
		long tc3e = System.currentTimeMillis();

        System.out.println("matches: " + found);
	}

    public static void main(String[] args)
    {
        init();
        System.out.println("APSI");
        String[] serverIds;
		String[] clientIds;
        BigInteger no = new BigInteger("0");
		try{
			MessageDigest md = MessageDigest.getInstance("MD5");
			byte[] messageDigest = md.digest("16".getBytes());
			no = new BigInteger(1,messageDigest);
		
			String s = no.toString();
			System.out.println("hash(16): " + s);
			
			Random rd = new Random(); 
		
		
			clientIds = new String[3];
            clientIds[0] = "5";
            clientIds[1] = "3";
            clientIds[2] = "18";
		
			
			serverIds = new String[2];
            serverIds[0] = "18";
            serverIds[1] = "2";
		
			
            perform(serverIds, clientIds);
		}
		catch(NoSuchAlgorithmException e){}
		
    }
    
}