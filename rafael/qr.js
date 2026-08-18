/* qr.js - Gerador de QR Code offline, sem CDN, sem dependência.
   Implementação mínima de QR Code modelo 2, byte mode, correção de erro nível M.
   Suporta versões 1-10 (até ~150 caracteres), suficiente para URLs curtas.

   Uso:  QR.desenhar(elementoCanvas, "https://exemplo.com", { escuro:"#0001AD", claro:"#FFFFFF", margem:4 })
        QR.paraPNG("https://exemplo.com", 1024, {...}) -> dataURL
*/
(function (global) {
  'use strict';

  // ---------- Campo de Galois GF(256) ----------
  var EXP = new Uint8Array(512), LOG = new Uint8Array(256);
  (function () {
    var x = 1;
    for (var i = 0; i < 255; i++) {
      EXP[i] = x; LOG[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= 0x11d;
    }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();

  function mul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function polyMul(a, b) {
    var r = new Uint8Array(a.length + b.length - 1);
    for (var i = 0; i < a.length; i++)
      for (var j = 0; j < b.length; j++)
        r[i + j] ^= mul(a[i], b[j]);
    return r;
  }

  function geradorRS(grau) {
    var g = new Uint8Array([1]);
    for (var i = 0; i < grau; i++) g = polyMul(g, new Uint8Array([1, EXP[i]]));
    return g;
  }

  function restoRS(dados, grau) {
    var g = geradorRS(grau);
    var buf = new Uint8Array(dados.length + grau);
    buf.set(dados);
    for (var i = 0; i < dados.length; i++) {
      var c = buf[i];
      if (c === 0) continue;
      for (var j = 0; j < g.length; j++) buf[i + j] ^= mul(g[j], c);
    }
    return buf.slice(dados.length);
  }

  // ---------- Tabelas por versão (nível M) ----------
  // [total de codewords de dados, codewords EC por bloco, nº blocos grupo1, nº blocos grupo2]
  var TAB_M = {
    1:  [16,  10, 1, 0],
    2:  [28,  16, 1, 0],
    3:  [44,  26, 1, 0],
    4:  [64,  18, 2, 0],
    5:  [86,  24, 2, 0],
    6:  [108, 16, 4, 0],
    7:  [124, 18, 4, 0],
    8:  [154, 22, 2, 2],
    9:  [182, 22, 3, 2],
    10: [216, 26, 4, 1]
  };

  var ALINHAMENTO = {
    1: [], 2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30],
    6: [6, 34], 7: [6, 22, 38], 8: [6, 24, 42], 9: [6, 26, 46], 10: [6, 28, 50]
  };

  function tamanho(v) { return v * 4 + 17; }

  function utf8Bytes(str) {
    var out = [], i, c;
    for (i = 0; i < str.length; i++) {
      c = str.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) { out.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f)); }
      else if (c < 0xd800 || c >= 0xe000) { out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f)); }
      else {
        i++;
        c = 0x10000 + (((c & 0x3ff) << 10) | (str.charCodeAt(i) & 0x3ff));
        out.push(0xf0 | (c >> 18), 0x80 | ((c >> 12) & 0x3f), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
      }
    }
    return out;
  }

  function escolherVersao(nBytes) {
    for (var v = 1; v <= 10; v++) {
      var cap = TAB_M[v][0];
      var bitsContagem = v < 10 ? 8 : 16;
      var necessario = 4 + bitsContagem + nBytes * 8;
      if (necessario <= cap * 8) return v;
    }
    throw new Error('Conteudo longo demais para QR versao 10 (nivel M). Encurte a URL.');
  }

  function montarCodewords(bytes, versao) {
    var info = TAB_M[versao];
    var totalDados = info[0];
    var bits = [];
    function push(valor, n) {
      for (var i = n - 1; i >= 0; i--) bits.push((valor >> i) & 1);
    }
    push(4, 4); // modo byte
    push(bytes.length, versao < 10 ? 8 : 16);
    for (var i = 0; i < bytes.length; i++) push(bytes[i], 8);

    // terminador
    var sobra = totalDados * 8 - bits.length;
    push(0, Math.min(4, sobra));
    while (bits.length % 8 !== 0) bits.push(0);

    var dados = [];
    for (var b = 0; b < bits.length; b += 8) {
      var v = 0;
      for (var k = 0; k < 8; k++) v = (v << 1) | bits[b + k];
      dados.push(v);
    }
    var pad = [0xec, 0x11], p = 0;
    while (dados.length < totalDados) dados.push(pad[p++ % 2]);
    return new Uint8Array(dados);
  }

  function intercalar(dados, versao) {
    var info = TAB_M[versao];
    var ecPorBloco = info[1], g1 = info[2], g2 = info[3];
    var totalBlocos = g1 + g2;
    var base = Math.floor(dados.length / totalBlocos);
    var blocos = [], ecs = [], pos = 0, i;

    for (i = 0; i < totalBlocos; i++) {
      var tam = base + (i >= g1 ? 1 : 0);
      var bloco = dados.slice(pos, pos + tam);
      pos += tam;
      blocos.push(bloco);
      ecs.push(restoRS(bloco, ecPorBloco));
    }

    var saida = [], maxD = 0;
    for (i = 0; i < blocos.length; i++) maxD = Math.max(maxD, blocos[i].length);
    for (var c = 0; c < maxD; c++)
      for (i = 0; i < blocos.length; i++)
        if (c < blocos[i].length) saida.push(blocos[i][c]);
    for (var e = 0; e < ecPorBloco; e++)
      for (i = 0; i < ecs.length; i++)
        saida.push(ecs[i][e]);
    return saida;
  }

  // ---------- Matriz ----------
  function novaMatriz(n) {
    var m = [];
    for (var i = 0; i < n; i++) {
      m.push(new Int8Array(n));
      for (var j = 0; j < n; j++) m[i][j] = -1; // -1 = livre
    }
    return m;
  }

  function porFinder(m, linha, col) {
    for (var r = -1; r <= 7; r++)
      for (var c = -1; c <= 7; c++) {
        var rr = linha + r, cc = col + c;
        if (rr < 0 || cc < 0 || rr >= m.length || cc >= m.length) continue;
        var borda = (r === -1 || r === 7 || c === -1 || c === 7);
        var externo = (r >= 0 && r <= 6 && (c === 0 || c === 6)) || (c >= 0 && c <= 6 && (r === 0 || r === 6));
        var interno = (r >= 2 && r <= 4 && c >= 2 && c <= 4);
        m[rr][cc] = borda ? 0 : (externo || interno ? 1 : 0);
      }
  }

  function porAlinhamento(m, versao) {
    var pos = ALINHAMENTO[versao], n = m.length;
    for (var a = 0; a < pos.length; a++)
      for (var b = 0; b < pos.length; b++) {
        var r = pos[a], c = pos[b];
        // pula onde colidiria com os finders
        if ((r <= 8 && c <= 8) || (r <= 8 && c >= n - 9) || (r >= n - 9 && c <= 8)) continue;
        for (var dr = -2; dr <= 2; dr++)
          for (var dc = -2; dc <= 2; dc++)
            m[r + dr][c + dc] = (Math.max(Math.abs(dr), Math.abs(dc)) !== 1) ? 1 : 0;
      }
  }

  function porTiming(m) {
    var n = m.length;
    for (var i = 8; i < n - 8; i++) {
      var v = (i % 2 === 0) ? 1 : 0;
      if (m[6][i] === -1) m[6][i] = v;
      if (m[i][6] === -1) m[i][6] = v;
    }
  }

  function reservarFormato(m) {
    var n = m.length, i;
    for (i = 0; i <= 8; i++) {
      if (m[8][i] === -1) m[8][i] = 0;
      if (m[i][8] === -1) m[i][8] = 0;
    }
    for (i = 0; i < 8; i++) {
      if (m[8][n - 1 - i] === -1) m[8][n - 1 - i] = 0;
      if (m[n - 1 - i][8] === -1) m[n - 1 - i][8] = 0;
    }
    m[n - 8][8] = 1; // módulo escuro fixo
  }

  function preencherDados(m, cw) {
    var n = m.length, bitIdx = 0, subindo = true;
    var total = cw.length * 8;
    function bit(i) { return (cw[i >> 3] >> (7 - (i & 7))) & 1; }

    for (var col = n - 1; col > 0; col -= 2) {
      if (col === 6) col--; // pula coluna de timing
      for (var passo = 0; passo < n; passo++) {
        var linha = subindo ? (n - 1 - passo) : passo;
        for (var d = 0; d < 2; d++) {
          var c = col - d;
          if (m[linha][c] !== -1) continue;
          m[linha][c] = bitIdx < total ? bit(bitIdx) : 0;
          bitIdx++;
        }
      }
      subindo = !subindo;
    }
  }

  function mascarar(m, reservado, mascara) {
    var n = m.length;
    for (var r = 0; r < n; r++)
      for (var c = 0; c < n; c++) {
        if (reservado[r][c]) continue;
        var inverter = false;
        switch (mascara) {
          case 0: inverter = ((r + c) % 2 === 0); break;
          case 1: inverter = (r % 2 === 0); break;
          case 2: inverter = (c % 3 === 0); break;
          case 3: inverter = ((r + c) % 3 === 0); break;
          case 4: inverter = ((Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0); break;
          case 5: inverter = (((r * c) % 2) + ((r * c) % 3) === 0); break;
          case 6: inverter = ((((r * c) % 2) + ((r * c) % 3)) % 2 === 0); break;
          case 7: inverter = ((((r + c) % 2) + ((r * c) % 3)) % 2 === 0); break;
        }
        if (inverter) m[r][c] ^= 1;
      }
  }

  function bitsFormato(mascara) {
    // nível M = 00
    var dados = (0x00 << 3) | mascara;
    var v = dados << 10;
    for (var i = 4; i >= 0; i--)
      if ((v >> (i + 10)) & 1) v ^= 0x537 << i;
    return ((dados << 10) | v) ^ 0x5412;
  }

  function porFormato(m, mascara) {
    var n = m.length, f = bitsFormato(mascara), i;
    for (i = 0; i <= 5; i++) m[8][i] = (f >> i) & 1;
    m[8][7] = (f >> 6) & 1;
    m[8][8] = (f >> 7) & 1;
    m[7][8] = (f >> 8) & 1;
    for (i = 9; i <= 14; i++) m[14 - i][8] = (f >> i) & 1;
    for (i = 0; i <= 7; i++) m[n - 1 - i][8] = (f >> i) & 1;
    for (i = 8; i <= 14; i++) m[8][n - 15 + i] = (f >> i) & 1;
    m[n - 8][8] = 1;
  }

  function penalidade(m) {
    var n = m.length, p = 0, r, c, i;
    // regra 1: sequências de 5+
    for (r = 0; r < n; r++)
      for (var dir = 0; dir < 2; dir++) {
        var cont = 1, ant = -1;
        for (c = 0; c < n; c++) {
          var v = dir === 0 ? m[r][c] : m[c][r];
          if (v === ant) { cont++; if (cont === 5) p += 3; else if (cont > 5) p++; }
          else { cont = 1; ant = v; }
        }
      }
    // regra 2: blocos 2x2
    for (r = 0; r < n - 1; r++)
      for (c = 0; c < n - 1; c++) {
        var a = m[r][c];
        if (a === m[r][c + 1] && a === m[r + 1][c] && a === m[r + 1][c + 1]) p += 3;
      }
    // regra 4: proporção escuro/claro
    var escuros = 0;
    for (r = 0; r < n; r++) for (c = 0; c < n; c++) if (m[r][c]) escuros++;
    var pct = (escuros * 100) / (n * n);
    p += Math.floor(Math.abs(pct - 50) / 5) * 10;
    return p;
  }

  function gerar(texto) {
    var bytes = utf8Bytes(texto);
    var versao = escolherVersao(bytes.length);
    var n = tamanho(versao);
    var m = novaMatriz(n);

    porFinder(m, 0, 0);
    porFinder(m, 0, n - 7);
    porFinder(m, n - 7, 0);
    porAlinhamento(m, versao);
    porTiming(m);
    reservarFormato(m);

    // guarda o que é função (reservado) antes de escrever dados
    var reservado = [];
    for (var r = 0; r < n; r++) {
      reservado.push(new Int8Array(n));
      for (var c = 0; c < n; c++) reservado[r][c] = m[r][c] !== -1 ? 1 : 0;
    }

    var cw = intercalar(montarCodewords(bytes, versao), versao);
    preencherDados(m, cw);

    // escolhe a melhor máscara
    var melhor = null, melhorP = Infinity;
    for (var k = 0; k < 8; k++) {
      var teste = m.map(function (l) { return Int8Array.from(l); });
      mascarar(teste, reservado, k);
      porFormato(teste, k);
      var p = penalidade(teste);
      if (p < melhorP) { melhorP = p; melhor = teste; }
    }
    return melhor;
  }

  function desenhar(canvas, texto, opcoes) {
    opcoes = opcoes || {};
    var escuro = opcoes.escuro || '#000000';
    var claro = opcoes.claro || '#FFFFFF';
    var margem = opcoes.margem == null ? 4 : opcoes.margem;

    var m = gerar(texto);
    var n = m.length;
    var lado = canvas.width || 512;
    canvas.height = lado;
    var escala = Math.floor(lado / (n + margem * 2));
    if (escala < 1) escala = 1;
    var real = escala * (n + margem * 2);

    canvas.width = real; canvas.height = real;
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = claro;
    ctx.fillRect(0, 0, real, real);
    ctx.fillStyle = escuro;
    for (var r = 0; r < n; r++)
      for (var c = 0; c < n; c++)
        if (m[r][c])
          ctx.fillRect((c + margem) * escala, (r + margem) * escala, escala, escala);
    return canvas;
  }

  function paraPNG(texto, lado, opcoes) {
    var cv = document.createElement('canvas');
    cv.width = lado || 1024;
    desenhar(cv, texto, opcoes);
    return cv.toDataURL('image/png');
  }

  global.QR = { gerar: gerar, desenhar: desenhar, paraPNG: paraPNG };
})(window);
