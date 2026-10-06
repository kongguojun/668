# -*- coding: utf-8 -*-
import base64 as _RUuby
import zlib as _NBixrt
_TEmbk = 1353703779
_AHmq = 1021839715
def _MZjcd(d, k):
    return bytes(c ^ k for c in d)
_JXjgs = lambda d, k: _MZjcd(_RUuby.b64decode(d), k).decode('utf-8')
_DZmgb = lambda d, k: _MZjcd(_RUuby.b64decode(d), k)[::-1].decode('utf-8')
_NQws = lambda d, k: _MZjcd(bytes.fromhex(d), k).decode('utf-8')
_DGhquc = lambda d, k: _NBixrt.decompress(_MZjcd(_RUuby.b64decode(d), k)).decode('utf-8')
def _CGuet(n):
    try:
        d = _LQiw[n]
        k = (((_TEmbk ^ (n * 2654435761)) >> (n & 7)) & 255) ^ (((n << 3) ^ _AHmq) & 255)
        if k == 0:
            k = 158
        return (_JXjgs, _DZmgb, _NQws, _DGhquc)[(n ^ _AHmq) & 3](d, k)
    except Exception:
        return ''
_LQiw = [b'\xe1\xdd\xa1\xd0\x02\xd8\xd0\xeaB]U2/Pa\xc7\xec\xb5\xee\xea\x83C\xee{M\xde"\xc8\x98\xc2\xc9\xb4\xe6\x08e\x1a7\xa2n\x98\xca6B,\xdf\x83\xfa', '746b72517663767771', '1w==', 'h5qZkLuUmJA=', 'QePy9vcREBDpDugKDesKOTkZrDrU', '60', '28rf+trQ+87XyM0=', 'bnV9bR0GHhMAHhZQEh5bEh5aFx4eFtuxlNuxqNaZnduRuNi3vteivtqGt9efhxc=', 'sBLj5uXgAOfiObjJyNtHy2I=', b'\xbbu\x9a+\xf5\xfc;n\xb3\xbb\xb6', 'InRxayM+IyM0cXgidHk9PTAyDnEMMCQZODQXCg==', 'FAsXEA==', 'KYsaGH0YfVdRV19TXw==', '0a010c1d161f1b3a1d03', b'[(\x0c\x8a\x07\x8f?', 'pqY=', '6Eq7X7/auZaQljWSoA==', '59555e5f', 'aA==', '6+Tq4eax4ubn4+ri4eHmtbfm47fm67bk5rfktrfntuuysLbh6+Hr4rLl4eGxsOGxsObn6uW347LitbHh4OKy67XrtbCw4Oa2suOw4La35+G36+CxtrWxt+DntbDl6+Xi5evisLbisrbm4+Sx4+Dh4eHnt+Oysbfn5OXqteDgt+rg5+PlsLWysea3trWx4eLnsLKx4OC34bLr4eTjtbLg5LDgtuPr4uHi5ee2serl4bfq4rGw5Oritebg5bWx4rCy6+br4rbh5urg5+a2sba26+TnsuHr5+W25uLr5+Xk5uPh5ePl47Xm4uGw5eTqt+Pm4eSwtubkt+Ll4efn6rG367Gwt+S15uXq5+Dn6+Xk5Oew5Ou347a2seW35LGx67DlsOLi5eTn5Oe25ee3tuuytrXn5Lbn4+Hg6uPn6+C347bm5ODmturm5uHrsLHgsue14Lbn4OLm4uPl6+frsOLn5+ey6uHmseayt+Xi4OfqtbLn57Hn5LG34eu247a15uqxsLe14La3srbjsbK35erg4+C2tuvnseDk4LXg5rHh5bXmsevk4rLl5ePrsrbh67G2suLmtePnsOHr4Ormt7a2t+O35bbmseK35LXkteTh5OPkt7HmtuO3sOG26uHjsLeysOOy4OLl47fjseXn5be25rHltbCx6uDi6+qx5Ovh4+S3tevgt+K3t+u24uLgsOSy4bfh4OG357Xh4ODgtbbi6ubh4+vgsLLqt7Di4uri4raysrHk57Hh5rK2srWy4bDl4eCx5uCysrLisOu36uLlsOTkteHht+Ox5Lfqtern4+u3t+Tm5eW3teDjt+Ky6+vl4+HqtrW3t+Pkt+rk5uPq4uW14uex4+K24+Ox5rHntuXi4urj67Xksuvg47Di5ODl5+Xl4+S1teC1suvm4+Tj6+e15+K14+Titerl4OC25uDi4bGx5bbht+Gx5+Lj57bqt+bg5erg5OTj67Xr4LHh57blsrXh6+C14rbr67Xq5OOwsOfj4OXmtuG3teSwtbHhsea267C36+Gy5bay5rGxtuqw5ubm5ubrteS25rLn5Oe3traw4eewt7Xr5eXm4ubg67bm5OPlseaysebgtuuw6uLlsuLmt+DgsObj6uPm6+uytuqw4+Hk5rLi5LeysuHgsOTk47Xn47C14rfkt7fi5rex4+fi5rHhtrC35OXg6rG15+SxtrG3sebltergsuHl5+u36rXq5uvl5+fj4+Ox6rfgsuPq4uPgseXl5Ovj5bfmseq15+rm6uPgsrG3t+fqseCx4rLl4eLi4Lfl4OKw5+rnsrK15uvl6uvjtebl4LLi5ee1sLWy6ubktuO14uOy5Org4Lbm6+bl4ODk5OXm6+a34uC36+C14Lbg47C24efn4evk4efqsrfjtuvk6+Lq4OHnsLCxt+Dm4Oe24uHjsOrm5+frsLDmsubm4LLksue2t7W15+Th4bLm67ax4+W36+Tr4uGx6uextbHn5ePq4OXq6rbj4evjseqy6urrtuKyt7Dq5LbrsLWw6+CxtuPq5ubm5eC35+bg4uDj6+Xh5rDq5Lfm6urnseuwsuLkterg6uK14uHi4Oa36uGy5rfr4uW26uPh6rG24OLh6+rr6uCw6uW16uXm47ew4eLr6+rh4OXm4eLr5uuyteO24LK2tuvg5rKysrfj4+rht7eysrHg4ra1t+bgt+Xm5Ofm4+A=', b'./_\xba\xb4\xbbq\xda\xa9\x19\xa4\xdf\x195u-\xd3\t', '6c7d7b797f73697268', '7vDX++Pu8g==', 'p6yltLChtoqlqaE=', 'IIJzkxQRla+UE5N3XlhOJFxP', '48515a61575a', 'ZjA1L2d6Z2dwNWFlbGd2cHE1eWdgNUh0YF18cFNO', 'GA==', b'\x16\xa5&\x8a\xfd\xee\xc8&\xc93\xbd\x82\x84\x8a', 'f9f8f0f8b8', b"\x04\x1b\xfb\xa0\xe9\x1a\x13\x83 \xbfw'\xd8\xe2\xa5x\xac\xdf\xcd\x0c\x80\x8eb}'<\xef\xfd{", 'emdESGlUQHwBRURVQEhNYk5PVURPVQFEU1NOUxs=', 'WPpb+pHB+bzZIC91JB8=', '00', 'LjsyHzsiPQ==', b"\xaa\xfb\xbb\x9b\xdd|#esr\xb2\xff2\x85\xa6\xc6\x14\xcf\x85\xb6\xd8\xfe\xc1S\x9f\xbc'\xaf\xbf", '40Fgq+R5X7zg/aYGo9gug5utnZwJ', '969b9b9fb89d8780', '8ufuw7rj+fLj+fjU', 'x8PDz/ztw8jLzsvEyO3h++Lh482z/brIy9vPzMvL2cnIwe397e3Z4cvtz8vL5cPIy9vJ5OTr6PvQ3u6+vcHG6OfooevBzsbOxfniwfLm5d+h4sv73N7txb26uL/v7bLkwOT46frCxN3Fu8C9xfPM6ceh+ujMs/rM46XJ+8Td5Obf8+PNpbPf+e+/083uyMzm5uDi/Mzzvb7i/fvpwt7z2vnh2sO9/Pu5u8C4ud3ZwtDv+dy94rPY59C5z9z9/c3JwP7Au866uuzspbPp2r/nvt+lvuC56OzEwuHew8a9s+HM+r/Nw9rJ4+jTzeLC2//J07u+3PzgxPnz07Oy0OL88qGy8+bB5vLnx8/A+eXBvtnNuLvb+bzy6LzP083Dy/z+uun45Mzt29L87dy5/aX8utjizrPLwcnh4NDFs+Xr7rjssvD/4vvZ+/2y+/zj+N3f8tPQ8MLfx83due6yz/DAuP3Tpcb+v+Xe8LviyObkuuPtyOvJ5bPuvuu/wPvp88/buu6l/f+9sujL7cfIy8vPye3tz8vTw9rmpePiz8Tv8s/6+8m67s3o6NrIzdPO0rzO5uT76NLm3v7wvMW8wMHtzM28usb7y/7M5eXwx8DH/uvk39PO5rj6ufmlvv7n397j6eD+7sDp6e3gs+fmpcDu2svZ4Pi5y9vP7vzfzuLs/sbz27zOobz75d/o/fjJx7vQx937yNznu97av+3n8sbl48Lw48Tg2v2l4bng0vvEuPPs3sDTxrnw3aXm2c/mwdqh5trA3ebP8O//2Nv749LF4LzO2+O4yPzN5+3F/9ml/7zG4uDEuOHc3MHy5cO8uP347/O67Pyl48TCv/PI8/vzwsLf/cvPzMHhv+G+2r7C0t/TzcfP4rnZ8MH6y9jdzr7w2sTB0MXC7vrr8+TbvOu/86H++MG50/29yN/h3c673Ni84sDe0Lzy+f7w+Lvd3+2408657sfn2OTLvcbz5e3/pe7uxfj/oaHP2dvByO3bzrLh2rntyPv43LPCxNrwx7/j0tDLz8LY/rrA497s5fP7ssHzvb7948Xo4qXN5//T4sHo0Nja0/3nz+O5wOG428yz5rzfpfyl8OHzybulxd3c8v3i0uDvxfLi27Li7sDz5s3p/vq97P6y3e68zfu44sH9/cHG8v3A5b7wpdjf79voxuu82uDgxc/Z68v678HN6ebazszI6P3a6LvL2uff+P3ozM7v/+n9z77A/cHI7dvJ+r/bzeHJ6/77ofm5u/O//LnQ3LnN28HAss7H/My/zsLJ+8Ps+M/53r3Y7b6/ue2/8r7Z4sv/5d/Mxdq83v/wwPjk4fL4zsbY2cj++fvewcyz7NjJ5v7eu+nDvejz4eHY88Lo29/fzM7u/My++/DH38u9+d/Y6f+9vLrb/+a9vLPS2svkvfvIxKHY8v7tutnH4+LT89q7//7g4MPEy/ze4fns+sC478G+zL3bwcjt287svenSwL3Es+e7u+/+/v2/s9zJ+f/N5ePFusP4sr/S2/nQ6N+z8tjEyMvB393ivt6/2cLB5e/P8+fL79/luMXQ4Ojjwcbi3se//MXk+rvapc3s++Lu48PpssbQ6OffwdjuuLPH/+C48sPY39zC6cjTzcTB0s6/5vrd68b67+n877PapcnHpe3mw8vl+6H+xKXF/+jNwcbMuObvzsfPstrC+/vNy6HL69ziwtvByO3P0uT/+Mfr0rnb0t37xefp6OL4s/Ls68jDzPPr5766+sTw+vq5xPnEvLrP78zlxsHk+ubDx87y7OHQ3Ljw+snG4b3m8tClxeDN//iy5dPCwuzF6+3OusX9pbzg57jc08zuuLj688v55aXmvvLnv/q987jiz93mwea769v70sja5NnL2PDgws/Zxs/Fv9uyztr777n+svKl+M6yvbqyudjg4Mbn++jP4uf55sDL5c3Iy8fa28Xdv+K8/OLj49v9/7zp0NuyydzO3v3O3uHN+aHOpe/h/cHjy+Xj2t7y4tnTy8Tz8rzy37rlvdn7zejAv+z4vsDw+cXbpcvo6bnMwvDMy7nF8Oz9vuS+y/Da4vzj69vo/cy7s97A58Pl4dK42P2l6+KhvsvT+MLmpeDC79ra58bZ8r/9s/zA/8el48e93vn9uL77+fvNxb7uvdnc2+7kzP/w4cXmubnB2Q==', 'kDKT1pcFOyYN6OdP7KE=', '43455344695f52', '3do=', '8vft6g==', 'y2l4nv20s7Eksvs=', b"'@\xd1\xb3\xb1*~qegA\x03%t\xa8T\x16\x86=\xfd\x86\xcc7\x19\xf4\xf2`\xf2\xa2", 'jYCVjpU=', 'Gx4aHgM=', 'yGqb+fyftrC0iLEA', '5c454e754b584f4b', '68b96vz6', 'cX5yeg==', '0nCBYeUjhWLmrKqheqhP', '3d2c3f3e28', 'lZSSj5KVkp2enw==', b'\x8a\xc8C\xeaE\x12JG\x9e\xb4\xeb\xc5\xa3\xd2k\xb0f\xd1\xff\x08\x7f\xab\xe0\x8c\x8a\x90L\xd3\x87\xe3\xa0\x98/G', 'AKKzUFFRUM6qrzezsVc3VTJUsKyz1jQxNqwztqs3VFCoVbM0MbWvVbBXUjG0qf8qsUHh0QFdgnj8sG2n', '58414a715d4d415c4b', 'CQIbxcyF+uWITVNATQILAyQGAgIP', 'iZSHng==', 'uhiJDIru6ovvMAvu7MPC2AzGRg==', '0c0b15', 'lIGUkQ==', 'z8jdyMnP', 'OJpzREBAckBy', b'\xb2\x80\xf1\xc4\xc6\t\xd3\xda\\', b'K$\xe91\x80Y\xf0\xd5ss\xd9', 'HxQa', 'Hb9kdmWJmpX64NqK3eqMxvuN79SA7MKA+d/sv2jC', 'cd9183c3ad92cd82b7c385a2c3b3a2c384ad1f05c199bfc0b4bd0ac0ad95c3b9ba0acdaf94c2b686c198bccc87b8', b'2\x13\x81$\xb2\x82\xa4\xc4', 'TGp8azRYfnx3bQ==', '8FID/sNFfKDFBN0Ap0CnptnApaJCpzra2KWOiOMDgOQ=', '085255', 'REZAUQ==', 'K09hKlxQK1NhKUVr', 'Zcc2M1QxNDAT1DE1Gx0KthlY', '8a97b4b899a4b08cf1a1bdb0a8b4a392bebfa5b4bfa5f1b4a3a3bea3eb', 'qayyuri7', 'jYOHkuKuiqOxquKvq7Gvo7ahqg==', 'qAr7G59Z/xiZfFz//RrR0PAK1cE=', '3d59773c48773d45773f537d', 'RDFdS2Rxa2tBf3VFVlNzN1hFNzZpM0xk', 'AA==', 'TO5/+ht/GT57GDQ0OtE3fA==', '9d919a9b9d', b'\xcb\x85\xe2/\xbe#\xe5\x1e\x83\x94V\xbe\xb5\x15JZ\x83P\x7f\xf4I\x0e', '2cDL8NbKzt0=', b'\xdb\x03M\x04]K\x8a9\x92KcM}\xdbD\x1e+\x13\xfd\xa3\x7f\xa6\r\xc6C\xee}G():/\xb7\xda\x13CJ\xddI\x91', '3c31313517303831', 'iIqXg7qchImVuoGKkw==', 'SSo6Ty8nQh4JTwkaTDIkSSo7TDYGQh8uTBA6TT4bSSomTxolQiorQjMkSSonTy8nQh4TTyIsThABTD8eTTosRRYmThEvThQxThIAThAQTwcMThMKSSorThAOTB8rThIkTB8hQgU/ThcVTT4CRRYmQgUdThAkThc5QwAmTzokipieik8aJUw9HE8sL08iCkMzDkUWMUwjKkw2I08XG0INLE8sL08EE00jIkw3KU83LU8XOE8kNU0jIkw3KUw8E0wjKkw2I0UWJk4SD00MK00+Ak4QJE4REU4XP08/LE4SME0+AkMqPkUWJk8MKEw2I04UH0w3KUIFHU87IE01D08iCkMzDkkqKKCg', 'VPZn5+AFZQEGKiwnlS7W', '5c454e754e43584f495e4558', b'\xa9\n(\x06\xdfp\xcf\t\xbc \xb7\x82s\xb6\xc4P\xc8\xa1\x10L\xf9\xaa\xa0g\xec\xfb\xd0aN\x9e\xc7:', 'U05tYUB9aVUoa2l8bW9nenFLZ2Z8bWZ8KG16emd6Mg==', 'GLob0R6Xs54JT9ZMG7bRnRm31gdt7XoB/mGaT9pWXv/cmKm++U93rbU0GLRQJYG5vMVPujdJiHt6eHpL9HbHdhmGxYXnhRNJICE5BiEQKQIpCdH14uGNq9mT/oz5lRSCbGUjO2ijOsF4yKJVT6VF0US1Np0Jp+YHE4bL3zjYgpnyPU+W12NZtmrp2ZnFGUXWcNv/jgjkOG/XgbmGda86ms10Poz/mQymmgcTGv8WTRzeGp3zfb0vm0de/7WSHK6cx4uGIVzBw5DUH7VrwL9WLmU6AM2QwhmPs2mrPkw/nBIqQ2itDhteBUO86Md9K/7O+2VgO6L1GQ==', b'L\xe8\xea\xbb\xdf\x06\xe1\xc5\x13K\xab\xca\xc5z\xed+\xeb\x0b\x08_|,qk\xfc\xabMh4:\xed\xa6\x85\xab\x80\x89i\xca\xe0', b'$\xbe\xb6\xed\xb3(\xc9\x9dF\x9f\xa2\x03g]\xdf\x94\xa2t2\xfcn\xbd', 'ys/Qyebc190=', 'vx0Mj+sxDogJwcfM1cUB', 'bedce7b1c5f57325', 'VBQQEQ==', 'AxoRKhYaGwEQGwE=', '0HKDAYTgJWfkqaikiKpH', '7a', b'N@\xebC\xb2\xbc:\x8c\xcf\x0f\xd5\xc1\xf4\x80wG\x1fNyq\xed\x0f\t\xb7\x0f\xb4,\x16\x81<wTQ\xde5r\x8b\x1e\xe2\x9eon\x11\xb8\xed\xd2\xb4', '4Pz8+A==', 'B6VMzk9Xf399M35y', 'cac7c3c6', '0NHXyt3L2tHMytDX', 'Nj8tNjI3PA==', b'66\x13\x03\x0b\xae\xef\xf9\x82\xe9\x0f/\xc8\x038\xe9\x85\xec\xf1\x1bP\x91', '9a85999e22657d2c7b48f0eab8afbbbfafb9beb92e76522f4f42e6eabfb8a6a6a3a82f4f562f705feae22f64682c427d2d6165acafbea9a22f455b9a85999e2e72472f456523576ae3', '+vL+8cD78Ok=', 'tw==', b'\x90\xf1\xc2t\xc8\x8a\x172S\xda\xdf\xc9b\xad\x87\xcdt\x85\x05\xe8\x82J*\xca\xc0\x07\xf1\xea~\xa2\xe2\xb5\xae\xeb\x12\xa1s\xcf\t<', b'4\xa9P=%\x0c\x1a\xe9g\xc5>Q\x1d\x0en\xa3)#\x10\x87B\xb3t\xbb\xb96Z*\xf9', b'\xf6H\x0ebR\xde\xfc\xa0\xf9m9\x9bZ\xcf\x90\xd8\xba6\r4p\x83\x9d\xfaLJ?\xd9\x98\x98\xdc', 'BA==', 'QOKzTnP1zBB1tG0QdnUUcvZI9vcTcfUTaXAVEvIXijo4mFUy2A==', '38212a113c2b232f3c253d', 'AAbj5pjpwpXYyZXM2ZhdRgkeFBn/zJj4+5jj5pjpwpVdUenHmPDumPvSmN7alV1DUF3/zJvK0pX70pjd95g=', '4P/myeLv5vM=', '9lSP2I4nccbLz8quaC4vZyQCaBAKZw4uawk0aRQKaRU6Zx0waBYhax4oawEhajYFpmsqCWo1M83KwGshN2o2A2sjFmsSJqFpIzBrHgNqNgNpIihmMRprFRC6vr2n26e4aQ==', '3d4d6b3e527c3f63513c6164', b'\x89\xcc\x12\xf9\xa7\x8c\x19\x83\xbb6p:', 'h4yFlJCBlq2Kgos=', '+Fr7MudWUwmzHvbs+LbnvoC4YIgH', 'b4aba6a7ad97b0ae94ad', b'\x82\x8dx\x1e\x03\x0b\xfc\x19\xa5,\xe3:R\x9b\xbe\xc2\xc6\x8f\xe3\x06\x03gw', '75GMkYmA38UMRnsNb1QAbEIAeV/vjYqWkd/FjZGRlZbfysqDiYqSgJeElYzLjpyBhoTLhovK7w1KUQN9a9/Fo4qLgqiMyqquAFhUDUJjxbWckY2Ki8W2lYyBgJcKWW0CekgAbEKklZXFpLWsA191xSdSxaSgtgBgTQx2Ww1SSsUnUsWIldECflEMdlsCREkNQkYKWWzvAnFNA1Zw38UBXWvFo5eAgKquy4+WiovFAHVpAn5LAFhwCllpAk58AmdcDGBoAlhLxZ7HjoCcx9/Ho4CMrZCEx8nHi4SIgMffxxV6YFoKXWoMRnsNb1QAbEIAeV/HyceRnJWAx9/WyceElYzH38fLyqOAjK2QhMuVnMfJx5aAhJeGjYSHiYDH39TJx5SQjIaOtoCEl4aNx9/UyceDjImRgJeEh4mAx9/VyceViYScgJemiouRgIuRx9/UmO8MZWMAdXTfxYaKiMuBn42Ki4LLg42PhsXKxYSVjJCVgYqSi4CBhpeclZHFxaSgtsjU193Ipqem78XFxcXFxa6gvNiBjKXBn7uKwcaDpcG7kKWPxcWss9iBn4OlwbuQpY+QhrulwcbBxcUNSlIDVGfYjYCdAEpjA3NiAVh2xQB2aABfcdiBhJGEAEhyA0tQjYCdAEpjA3Ni78XFxcXFxQBgSQBqZwBBUcWBhJGElsqWkcqWkdTFAV1fDUtbAEFiAkhbAHVoycUAS3sDUG4DeWgAb0QCTkoBXmADRUQMT2kASH0AeU0DZULJxQBqSgB+XwBLfwBBaAJxTe8Da0AAakbfxcrU19XUA0N5AGhwxcrU19XWA3V5AlFHxcrU1tXWA3dIA3FbzQB1TgJ+UQx2W8zFytTW1dECTkUNb2cAbXINRE3vsLepDUJGAEpj38XK1NbV1sUNWnEAfnsCf2HFk4yBgIqsi4OKlr64y5CXicUAeU3FgIuGl5yVkbCXidjY1MUDclMBXV/Ft7akxQBKYwNzYu/FxcXFxcWGiojLgZ/Lh5CWjIuAlpbLh4SWgMuQkYyJlsuCqcuxzczFAGNgAlhLxbWuprbG3cUCQmQMd0DvxcXFxcXFgqnLgZ+DhIuNkITNzMXI28W3tqTKoKanyqqkoLW1hIGBjIuCxc22raTI1MXOxaiio9TItq2k1MzFDUJGAEpj78XFxcXFxQ1CRgBKYwB1awBoVgBLaQNwUcWIldHFAn5RDHZbzQB1TgxxZABLfwx+Y8zJxQBLRwNtUgJOSgFefQ1RXABHfABqTwBtQcWGioGAypGXnLWJhJysi4OKs4rv', '2XvaGNl/Kg8s7po2njwSqqGZHak/', 'efb5b1b3', 'bnl4fXl0', '8vfxsQ==', 'MJIDgoeHvgRJSEA4ShE=', '2d233f11293422', b'\x8b%\x8c<\x16\xaa\x88\xe31\x0fN\xc9\xa5\xe2\x93\xce\xd6\xbc\xe7\x98\x7f\xa8\xd9\x12\xf9\x7f\x1f\x93Q', 'BwEEBBsGAEZCQQ==', b'\\\n\xad\xf2\xd4\r\x1f+F}\xd22\xc4\x1aP\x9f{\n\xcb\xa7j\x1d\x93\x89\xf6\xdaW"=\x0f)\xf9\xb1\x9dA\x98\xa1K\xde\xf1\xaai\xce\xbc\x19*', '44', 'KAV/Ig1xtqLm+7YRAHAYDnAsEXM1MX62uhEAcBA5c7a/xtPX2buuoqaku9fFxL6ioPPl9/S2LC5ytvrk47YgAXC2p6ur+uTD4ubv5PX48w==', 'SV9YWE9EXmlCS1peT1hjTg==', 'aMrjZ2QdQCC4ICBEOF49WDxaPNk/QtjbP0FY2z/dWxEQmIgZ/Q==', '99958a838d88938e93949d', 'Y2duZXR5JmV4cW4mfGAmeSYiYiJjJns=', 'JkZr5rAqWEU=', 'CKpbXT5dgrw7u3+7d3BmuXRh', b"\xfa\xc6\x03\x856\xe7\xd8`9g\xabO\xe9I\xc5E\xbav\xa3fUQju'\xfb\xca\x98\xcb5\xa3\x85\xff\xda\xde\xec\xcd", 'E0Xh9IlP5vuJE0XR5YU=', b'\xab<\xa8\x12\xeav\xe9>\xfa\xf7\r', b'd\xd7\xe7\xbdu\xd8%\xc1\x0bsX!\xfa&\xb5\xfdeh', '5b0d445b0d', 'zYDGmNs=', 'fQ==', 'kDLDI8Rgx8ahxMHF7uj/S+y7', 'efe0edffff', 'HwgVFB0T', 'AhEeGzwZAwQ=', b'1\xd1\xaf\xc2\xc8Y\xb4\xb4\x9c"\xe1\xd2\xf9\xb9!\xd7\xee\xa1\xcd*\xb3\xb7t\xa0F\x1eY\x05\xc5=\xf1|', '849d96ad9391869d80', 'yN3K', 'SUBSbE5TRA==', 'e9lIzUsvK0ou8U8CAxEsAJY=', b'\x06a\x97\xbf\x0e\n\x92\x82jH?\x8e\x9f\xee `H`\xa9\xfaQFK\xfbL\xf5d\xdf\x1f\xf4\x80C-p^\x95\x0e\xf5\x1b\x87\xb1\xa4H', 'BlBIEgYYVQZQSBARGhZVBhoTGzwaEBEcA1UaG1UoFAA9HBAzLg==', 'czAtaQ==', 'ELIjpKVHpUNpaGCwav0=', '1419191d38171b13', 'uP36', 'FUMUFUNvFUM=', 'Q+FwFxPz8nd1F/L39Oj0EfX0iG1z9XMXEXUWihYWcuiOOzv5ADCP', '909d9481bb8a858981', 'd2IpOzo=', b'\xad\xc6\x99v\r6\xbcu1N\xf3\x06\x1e\xca\xd6\x06\xe2\xcbA\xd1', 'SOq7Hxp+NDA0LTGW', 'ab89898f9a9ec7af8489858e83848d', 'n9/d2A==', 'IWljeQ==', 'qgiB/wSF/wTh5mLi+gL5fRji4OEDGf/iY4X/1NKFaNXS', '752a1b770634771f39791c01']

_CGuet(131)

import json
import binascii
import base64
import sys
import os

sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from base.spider import Spider as BaseSpider
except ImportError:
    class BaseSpider:
        def __init__(self, query_params=None, t4_api=None):
            self.query_params = query_params or {}
            self.t4_api = t4_api or ''
            self.extend = ''

        def fetch(self, url, params=None, headers=None, cookies=None, timeout=10, **kw):
            import requests
            return requests.post(url, data=params, headers=headers,
                                 cookies=cookies, timeout=timeout, verify=False)




_SBOX = [0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]
_INV_SBOX = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV_SBOX[_v] = _i
_RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]


def _xt(a):
    a <<= 1
    return (a ^ 0x1b) & 0xff if a & 0x100 else a


_M2 = [_xt(x) for x in range(256)]
_M3 = [_M2[x] ^ x for x in range(256)]
_M9, _M11, _M13, _M14 = [], [], [], []
for _x in range(256):
    _x2, _x4, _x8 = _M2[_x], _M2[_M2[_x]], _M2[_M2[_M2[_x]]]
    _M9.append(_x8 ^ _x)
    _M11.append(_x8 ^ _x2 ^ _x)
    _M13.append(_x8 ^ _x4 ^ _x)
    _M14.append(_x8 ^ _x4 ^ _x2)


def _expand(key):
    w = [list(key[4 * i:4 * i + 4]) for i in range(4)]
    for i in range(4, 44):
        t = list(w[i - 1])
        if i % 4 == 0:
            t = t[1:] + t[:1]
            t = [_SBOX[b] for b in t]
            t[0] ^= _RCON[i // 4 - 1]
        w.append([w[i - 4][j] ^ t[j] for j in range(4)])
    return w


def _ark(s, w, rnd):
    for c in range(4):
        wc = w[rnd * 4 + c]
        b = c * 4
        s[b] ^= wc[0]; s[b + 1] ^= wc[1]; s[b + 2] ^= wc[2]; s[b + 3] ^= wc[3]


def _sr(s):
    t = list(s)
    for r in range(1, 4):
        for c in range(4):
            s[c * 4 + r] = t[((c + r) % 4) * 4 + r]


def _isr(s):
    t = list(s)
    for r in range(1, 4):
        for c in range(4):
            s[c * 4 + r] = t[((c - r) % 4) * 4 + r]


def _mc(s):
    for c in range(4):
        a0, a1, a2, a3 = s[c * 4:c * 4 + 4]
        s[c * 4] = _M2[a0] ^ _M3[a1] ^ a2 ^ a3
        s[c * 4 + 1] = a0 ^ _M2[a1] ^ _M3[a2] ^ a3
        s[c * 4 + 2] = a0 ^ a1 ^ _M2[a2] ^ _M3[a3]
        s[c * 4 + 3] = _M3[a0] ^ a1 ^ a2 ^ _M2[a3]


def _imc(s):
    for c in range(4):
        a0, a1, a2, a3 = s[c * 4:c * 4 + 4]
        s[c * 4] = _M14[a0] ^ _M11[a1] ^ _M13[a2] ^ _M9[a3]
        s[c * 4 + 1] = _M9[a0] ^ _M14[a1] ^ _M11[a2] ^ _M13[a3]
        s[c * 4 + 2] = _M13[a0] ^ _M9[a1] ^ _M14[a2] ^ _M11[a3]
        s[c * 4 + 3] = _M11[a0] ^ _M13[a1] ^ _M9[a2] ^ _M14[a3]


def _eb(blk, w):
    s = list(blk)
    _ark(s, w, 0)
    for rnd in range(1, 10):
        s = [_SBOX[b] for b in s]
        _sr(s); _mc(s); _ark(s, w, rnd)
    s = [_SBOX[b] for b in s]
    _sr(s); _ark(s, w, 10)
    return s


def _db(blk, w):
    s = list(blk)
    _ark(s, w, 10)
    for rnd in range(9, 0, -1):
        _isr(s)
        s = [_INV_SBOX[b] for b in s]
        _ark(s, w, rnd)
        _imc(s)
    _isr(s)
    s = [_INV_SBOX[b] for b in s]
    _ark(s, w, 0)
    return s


def aes_cbc_enc(data, key, iv, w):
    padlen = 16 - len(data) % 16
    data = data + bytes([padlen]) * padlen
    out = bytearray()
    prev = iv
    for i in range(0, len(data), 16):
        blk = bytes(x ^ y for x, y in zip(data[i:i + 16], prev))
        c = _eb(blk, w)
        prev = bytes(c)
        out += prev
    return bytes(out)


def aes_cbc_dec(data, key, iv, w):
    out = bytearray()
    prev = iv
    for i in range(0, len(data), 16):
        blk = data[i:i + 16]
        p = _db(blk, w)
        out += bytes(x ^ y for x, y in zip(p, prev))
        prev = blk
    if out:
        p = out[-1]
        if 1 <= p <= 16 and len(out) >= p:
            out = out[:-p]
    return bytes(out)





_PRIV_B64 = (
    _CGuet(39))


def _der_read(buf, pos):
    tag = buf[pos]
    pos += 1
    ln = buf[pos]
    pos += 1
    if ln & 0x80:
        n = ln & 0x7F
        ln = int.from_bytes(buf[pos:pos + n], _CGuet(67))
        pos += n
    return tag, buf[pos:pos + ln], pos + ln


def _parse_pkcs8_rsa(der):
    _CGuet(7)
    _, body, _ = _der_read(der, 0)
    pos = 0
    _, _ver, pos = _der_read(body, pos)
    _, _alg, pos = _der_read(body, pos)
    _, octet, pos = _der_read(body, pos)
    _, rbody, _ = _der_read(octet, 0)
    p, vals = 0, []
    for _ in range(9):
        _, v, p = _der_read(rbody, p)
        vals.append(int.from_bytes(v, _CGuet(67)))
    return vals[1], vals[2], vals[3]   


def _mgf1(seed, length, hlen=20):
    out, c = b"", 0
    while len(out) < length:
        out += __import__(_CGuet(111)).sha1(seed + c.to_bytes(4, _CGuet(67))).digest()
        c += 1
    return out[:length]


def _oaep_decode(em, k, hlen=20):
    import hashlib
    masked_seed, masked_db = em[1:1 + hlen], em[1 + hlen:]
    seed = bytes(a ^ b for a, b in zip(masked_seed, _mgf1(masked_db, hlen, hlen)))
    db = bytes(a ^ b for a, b in zip(masked_db, _mgf1(seed, k - hlen - 1, hlen)))
    if db[:hlen] != hashlib.sha1(b"").digest():
        raise ValueError(_CGuet(79))
    i = hlen
    while i < len(db) and db[i] == 0:
        i += 1
    if i >= len(db) or db[i] != 1:
        raise ValueError(_CGuet(144))
    return db[i + 1:]


class _RSA:
    def __init__(self, b64key):
        self.n, self.e, self.d = _parse_pkcs8_rsa(base64.b64decode(b64key))
        self.k = (self.n.bit_length() + 7) // 8

    def decrypt(self, b64ct):
        c = int.from_bytes(base64.b64decode(b64ct), _CGuet(67))
        em = pow(c, self.d, self.n).to_bytes(self.k, _CGuet(67))
        return _oaep_decode(em, self.k)




class Spider(BaseSpider):
    API = _CGuet(56)
    UA = _CGuet(4)

    KEY = b"di@$z^o$#f@$^u@j"
    IV = b"dzf@$^u@juc^@$#$"

    
    DISCLAIMER = (_CGuet(91))

    
    DATAS = (_CGuet(19))
    ST = _CGuet(146)
    ST1 = _CGuet(82)

    def init(self, extend=""):
        self.extend = extend or ""
        self.timeout = 15
        self._w = _expand(self.KEY)   
        self._rsa = _RSA(_PRIV_B64)   
        self._cache = {}
        return {_CGuet(63): 0}

    def getName(self):
        return _CGuet(68)

    

    def _post(self, url, body_bytes, headers):
        _CGuet(113)
        try:
            import requests
            rsp = requests.post(url, data=body_bytes, headers=headers,
                                timeout=self.timeout, verify=False)
            return rsp.text or ""
        except Exception:
            pass
        try:
            import urllib.request
            import ssl
            req = urllib.request.Request(url, data=body_bytes, method=_CGuet(11),
                                         headers=headers)
            ctx = ssl._create_unverified_context()
            with urllib.request.urlopen(req, timeout=self.timeout, context=ctx) as r:
                raw = r.read()
            if raw[:2] == b"\x1f\x8b":   
                import gzip
                raw = gzip.decompress(raw)
            return raw.decode(_CGuet(174), _CGuet(158))
        except Exception as e:
            print(_CGuet(72) % e)
            return ""

    def _decode_url(self, url, encrypted=False):
        _CGuet(142)
        if not url:
            return url
        try:
            if not hasattr(self, _CGuet(176)) or self._rsa is None:
                self._rsa = _RSA(_PRIV_B64)
            
            if encrypted or (len(url) == 344 and url.endswith(_CGuet(15))):
                return self._rsa.decrypt(url).decode(_CGuet(174), _CGuet(158))
        except Exception as e:
            print(_CGuet(26) % e)
        return url

    def _call(self, num, obj):
        _CGuet(122)
        cache_key = _CGuet(153) % (num, json.dumps(obj, ensure_ascii=False, sort_keys=True))
        if cache_key in self._cache:
            return self._cache[cache_key]
        try:
            plain = json.dumps(obj, ensure_ascii=False, separators=(_CGuet(105), _CGuet(27))).encode(_CGuet(174))
            body = binascii.hexlify(aes_cbc_enc(plain, self.KEY, self.IV, self._w)).decode()
            headers = {
                _CGuet(71): self.UA,
                _CGuet(38): _CGuet(172),
                _CGuet(177): _CGuet(59),
                _CGuet(12): self.DATAS,
                _CGuet(42): self.ST,
                _CGuet(170): self.ST1,
            }
            text = self._post(self.API + str(num), body.encode(), headers)
            outer = json.loads(text)
            if not isinstance(outer, dict) or outer.get(_CGuet(17)) != 0:
                return {}
            data_hex = outer.get(_CGuet(62)) or ""
            if not data_hex:
                return {}
            pt = aes_cbc_dec(binascii.unhexlify(data_hex), self.KEY, self.IV, self._w)
            data = json.loads(pt.decode(_CGuet(174)))
            if len(self._cache) > 16:
                self._cache.clear()
            self._cache[cache_key] = data
            return data
        except Exception as e:
            print(_CGuet(10) % (num, e))
            return {}

    @staticmethod
    def _book2vod(b):
        _CGuet(58)
        return {
            _CGuet(25): str(b.get(_CGuet(136)) or ""),
            _CGuet(114): (b.get(_CGuet(169)) or "").strip(),
            _CGuet(52): b.get(_CGuet(84)) or "",
            _CGuet(121): b.get(_CGuet(76)) or "",
        }

    def _head_ok(self, url, timeout=15):
        _CGuet(124)
        if not url.startswith(_CGuet(107)):
            return False
        try:
            import ssl
            import urllib.request
            req = urllib.request.Request(url, method=_CGuet(109),
                                         headers={_CGuet(71): self.UA})
            ctx = ssl._create_unverified_context()
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as r:
                return 200 <= r.status < 300
        except Exception:
            return False

    def _rank(self):
        return self._call(1201, {})

    def _user(self):
        _CGuet(96)
        d = self._call(1013, {})
        u = d.get(_CGuet(148)) or {}
        return {
            _CGuet(156): u.get(_CGuet(1)) or 0,
            _CGuet(123): u.get(_CGuet(34)) or 0,
            _CGuet(99): u.get(_CGuet(6)) or "",
            _CGuet(168): u.get(_CGuet(168)) or 0,
            _CGuet(51): u.get(_CGuet(51)) or "",
            _CGuet(41): u.get(_CGuet(50)) or "",
        }

    def _acct_tag(self):
        _CGuet(69)
        try:
            u = self._user()
            if u[_CGuet(156)]:
                return _CGuet(36) % (u[_CGuet(99)] or "")
            if u[_CGuet(99)] and u[_CGuet(99)] != _CGuet(32):
                return _CGuet(128)
            return _CGuet(101) % u[_CGuet(168)]
        except Exception:
            return ""

    

    def homeContent(self, filter):
        classes = [
            {_CGuet(104): _CGuet(115), _CGuet(173): _CGuet(75)},
            {_CGuet(104): _CGuet(64), _CGuet(173): _CGuet(125)},
            {_CGuet(104): _CGuet(33), _CGuet(173): _CGuet(81)},
            {_CGuet(104): _CGuet(141), _CGuet(173): _CGuet(181)},
        ]
        return {_CGuet(157): classes, _CGuet(92): {}}

    def homeVideoContent(self):
        lst, seen = [], set()
        m = self._rank()
        for g in (m.get(_CGuet(159)) or []):
            for it in (g.get(_CGuet(37)) or []):
                b = it.get(_CGuet(89)) or it
                bid = str(b.get(_CGuet(136)) or "")
                if bid and bid not in seen:
                    seen.add(bid)
                    lst.append(self._book2vod(b))
        for w in (m.get(_CGuet(16)) or []):
            b = w.get(_CGuet(89)) or {}
            bid = str(b.get(_CGuet(136)) or "")
            if bid and bid not in seen:
                seen.add(bid)
                lst.append(self._book2vod(b))
        return {_CGuet(43): lst}

    

    def categoryContent(self, tid, pg, filter, extend):
        pg = max(1, int(pg or 1))
        lst = []
        try:
            m = self._rank()
            if tid == _CGuet(141):
                for w in (m.get(_CGuet(16)) or []):
                    b = w.get(_CGuet(89)) or {}
                    if b.get(_CGuet(136)):
                        v = self._book2vod(b)
                        v[_CGuet(121)] = (w.get(_CGuet(145)) or b.get(_CGuet(76)) or "")
                        lst.append(v)
            else:
                groups = m.get(_CGuet(159)) or []
                idx = int(tid) if str(tid).isdigit() else 0
                if 0 <= idx < len(groups):
                    for it in (groups[idx].get(_CGuet(37)) or []):
                        b = it.get(_CGuet(89)) or it
                        if b.get(_CGuet(136)):
                            lst.append(self._book2vod(b))
        except Exception as e:
            print(_CGuet(95), e)
        return {_CGuet(43): lst, _CGuet(74): 1, _CGuet(21): 1,
                _CGuet(47): max(1, len(lst)), _CGuet(46): len(lst)}

    

    def searchContent(self, key, quick, pg=1):
        try:
            if not key:
                return {_CGuet(43): []}
            pg = max(1, int(pg or 1))
            s = self._call(1203, {_CGuet(137): str(key), _CGuet(74): pg})
            bl = s.get(_CGuet(37)) or []
            lst = [self._book2vod(b) for b in bl if b.get(_CGuet(136))]
            has_more = bool(s.get(_CGuet(163)))
            return {_CGuet(43): lst, _CGuet(74): pg,
                    _CGuet(21): pg + 1 if has_more else pg,
                    _CGuet(47): 20, _CGuet(46): 999999 if has_more else len(lst)}
        except Exception as e:
            print(_CGuet(120), e)
            return {_CGuet(43): []}

    def searchContentPage(self, key, quick, pg):
        return self.searchContent(key, quick, pg)

    

    def _pick_first_id(self, ids):
        if isinstance(ids, list):
            return str(ids[0]) if ids else ""
        s = str(ids or "")
        if s.startswith(_CGuet(83)):
            try:
                arr = json.loads(s)
                if arr:
                    return str(arr[0])
            except Exception:
                pass
        return s

    def detailContent(self, ids):
        try:
            bid = self._pick_first_id(ids).strip().lstrip(_CGuet(155))
            if not bid:
                return {_CGuet(43): []}
            
            p = self._call(1303, {_CGuet(136): bid, _CGuet(164): "", _CGuet(139): 1})
            cur = str(p.get(_CGuet(143)) or "")
            
            c = self._call(1304, {_CGuet(136): bid, _CGuet(143): cur}) if cur else {}
            chs = c.get(_CGuet(60)) or []
            if not chs:
                return {_CGuet(43): []}

            bname = (c.get(_CGuet(169)) or p.get(_CGuet(169)) or "").strip()
            tags = c.get(_CGuet(48)) or []
            if isinstance(tags, list):
                type_name = _CGuet(155).join(str(t) for t in tags[:4])
            else:
                type_name = str(tags)

            
            parts = []
            for ch in chs:
                name = str(ch.get(_CGuet(23)) or "").replace(_CGuet(2), _CGuet(18))
                cid = str(ch.get(_CGuet(164)) or "")
                if cid:
                    parts.append(_CGuet(171) % (name, bid, cid))
            play_url = _CGuet(5).join(parts)

            lock = sum(1 for ch in chs if ch.get(_CGuet(100)))
            remarks = _CGuet(147) % len(chs) if not lock else _CGuet(150) % (len(chs), lock)

            vod = {
                _CGuet(25): bid,
                _CGuet(114): bname,
                _CGuet(52): c.get(_CGuet(84)) or p.get(_CGuet(84)) or "",
                _CGuet(173): type_name,
                _CGuet(87): "",
                _CGuet(49): _CGuet(40),
                _CGuet(121): remarks,
                _CGuet(57): "",
                _CGuet(93): "",
                _CGuet(161): (c.get(_CGuet(3)) or p.get(_CGuet(3)) or ""),
                _CGuet(103): self.DISCLAIMER + (c.get(_CGuet(110)) or p.get(_CGuet(110)) or "").strip(),
                _CGuet(90): _CGuet(132),
                _CGuet(80): play_url,
            }
            return {_CGuet(43): [vod]}
        except Exception as e:
            print(_CGuet(31), e)
            return {_CGuet(43): []}

    

    def playerContent(self, flag, vid, vip_flags):
        result = {_CGuet(53): 0, _CGuet(22): "", _CGuet(61): "", _CGuet(134): ""}
        try:
            pid = self._pick_first_id(vid).strip()
            if _CGuet(18) not in pid:
                return result
            bid, cid = pid.split(_CGuet(18), 1)
            
            p = self._call(1303, {_CGuet(136): bid, _CGuet(164): cid,
                                  _CGuet(139): 1, _CGuet(8): 1})
            ci = p.get(_CGuet(127)) or {}
            vv = ci.get(_CGuet(129)) or {}
            infos = vv.get(_CGuet(24)) or []
            if not infos:
                print(_CGuet(166) % (p.get(_CGuet(17)), p.get(_CGuet(44))))
                return result
            
            _rank = {_CGuet(29): 4, _CGuet(178): 3, _CGuet(102): 2, _CGuet(108): 1, _CGuet(135): 0}

            def _score(vi):
                d = _rank.get(str(vi.get(_CGuet(54)) or ""), -1)
                c = str(vi.get(_CGuet(85)) or "").lower()
                return (d, 0 if c.startswith((_CGuet(133), _CGuet(162))) else 1)

            
            dec = []
            for vi in sorted(infos, key=_score, reverse=True):
                enc = bool(vi.get(_CGuet(13)))
                dec.append({
                    _CGuet(54): str(vi.get(_CGuet(54)) or ""),
                    _CGuet(85): str(vi.get(_CGuet(85)) or ""),
                    _CGuet(61): self._decode_url(str(vi.get(_CGuet(61)) or "").strip(), enc),
                    _CGuet(78): self._decode_url(str(vi.get(_CGuet(78)) or "").strip(), enc),
                })

            chosen = ""

            
            for it in dec:
                if it[_CGuet(54)] == _CGuet(29) and it[_CGuet(61)].startswith(_CGuet(107)):
                    chosen = it[_CGuet(61)]
                    break

            
            
            
            if not chosen:
                cand = next((x for x in dec if x[_CGuet(54)] == _CGuet(178)
                             and _CGuet(119) in x[_CGuet(78)]), None)
                if cand is not None:
                    b = cand[_CGuet(78)]
                    base, q = b.split(_CGuet(119), 1)
                    u1080 = _CGuet(180) % (
                        base.rsplit(_CGuet(155), 1)[0], cid, q)
                    if self._head_ok(u1080):
                        chosen = u1080

            
            if not chosen:
                for it in dec:
                    if it[_CGuet(61)].startswith(_CGuet(107)):
                        chosen = it[_CGuet(61)]
                        break
            if not chosen:
                for it in dec:
                    if it[_CGuet(78)].startswith(_CGuet(107)):
                        chosen = it[_CGuet(78)]
                        break
            if not chosen:
                return result
            result[_CGuet(61)] = chosen
            result[_CGuet(134)] = json.dumps({_CGuet(71): self.UA}, ensure_ascii=False)
            return result
        except Exception as e:
            print(_CGuet(77), e)
            return result

    

    def isVideoFormat(self, url):
        u = (url or "").lower()
        return any(x in u for x in (_CGuet(154), _CGuet(167), _CGuet(179), _CGuet(73)))

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return None
